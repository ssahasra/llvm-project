//===- GenericCycleInfo.h - Control Flow Cycle Calculator -----------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// \brief Find all cycles in a control-flow graph, including irreducible loops.
///
/// Based on Havlak (1997), Nesting of Reducible and Irreducible Loops.
///
/// The term "cycle" is chosen to avoid a clash with the existing notion of
/// (natural) "loop".
///
/// Cycles are defined recursively:
///  1. The root "cycle" consists of all basic blocks of a function. Its header
///     is the entry block of the function.
///  2. The cycles nested inside a cycle C with header H are the maximal
///     non-trivial strongly connected components of the (induced) subgraph on
///     (C - H). (Non-trivial means that there must be an actual cycle, i.e.
///     a single basic blocks is only considered a cycle if it has a self-loop.)
///
/// Note: the C++ representation of the root "cycle" does _not_ contain an
/// explicit list of blocks, to avoid unnecessary memory use.
///
/// Every cycle has a \em header block, which is the target of a back edge in
/// the DFS tree chosen by the analysis.
///
/// Every cycle has one or more \em entry blocks, i.e. blocks with incoming
/// arcs from outside the cycle. The header block is the first entry block;
/// there is no order among the non-header entry blocks.
///
/// Warnings:
///  - Non-header entry blocks of a cycle can be contained in child cycles.
///  - Since the set of back edges depends on choices during a DFS (for
///    irreducible CFGs), there may be edges that "look like" back edges, but
///    whose destination block is not the header block of any cycle.
///
/// Some interesting properties:
///  - If the CFG is reducible, the cycles are exactly the natural loops and
///    every cycle has exactly one entry block.
///  - Cycles are well-nested (by definition).
///  - The entry blocks of a cycle are siblings in the dominator tree.
///  - The header of every natural loop is the header of some cycle (natural
///    loop back edges are back edges in _every_ choice of DFS tree). This
///    cycle is a superset of the natural loop.
///
/// Example (irreducible loop that contains natural loops; arcs are pointing
/// down unless indicated otherwise, brackets indicate self-loops):
///
///     |   |
///   />A] [B<\
///   |  \ /  |
///   ^---C---^
///       |
///
///   The self-loops of A and B give rise to two single-block natural loops.
///   A possible hierarchy of cycles is:
///   - cycle of blocks A, B, C, with A as header and B as additional entry
///     block; containing:
///   -- cycle of blocks B and C, with C as header and B as additional entry
///      block; containing
///   --- singleton cycle of block B
///   This hierarchy arises when DFS visits the blocks in the order A, C, B (in
///   preorder).
///
/// Example (irreducible loop as union of two natural loops):
///
///     |   |
///     A<->B
///     ^   ^
///     |   |
///     v   v
///     C   D
///     |   |
///
///   There are two natural loops: A, C and B, D.
///   A possible hierarchy of cycles is:
///   - cycle of blocks A, B, C, D, entry blocks A & B, with header A
///   -- cycle of blocks B, D, entry and header block B
///
/// Example (irreducible loop with "back edge" not necessarily pointing to a
/// header):
///
///     |   |
///    [A<--B<\
///     |     |
///     C-----^
///     |
///
///   The self-loop of A gives rise to a natural loop.
///   One possible cycle analysis is the following hierarchy:
///   - cycle of blocks A, B, C, with A and B as entry blocks and B as header
///   -- singleton cycle of block A
///   Another possible cycle analysis is result is that there is a single cycle
///   of blocks A, B, C, with A and B as entry blocks and A as header. The
///   presumed back edge C->B does not target a cycle header. This analysis
///   result occurs when the DFS visits the blocks in the order A, C, B (in
///   preorder).
///
/// Example (irreducible loop without any natural loops):
///
///     |   |
///   />A   B<\
///   | |\ /| |
///   | | x | |
///   | |/ \| |
///   ^-C   D-^
///     |   |
///
///   No natural loops, since A, B, C, D are siblings in the dominator tree.
///   A possible hierarchy of cycles is:
///   - cycle of blocks A, B, C, D, entry blocks A & B, with header A
///   -- cycle of blocks B, D, both as entry blocks, and D as header
///
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_GENERICCYCLEINFO_H
#define LLVM_GENERICCYCLEINFO_H

#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Printable.h"

#include <functional>
#include <vector>

namespace llvm {
template <typename BlockType> class GenericCycleInfo;
/// \brief base class for a cycle of basic blocks.
template <typename BlockType> class GenericCycle {
  friend class GenericCycleInfo<BlockType>;

protected:
  /// The parent cycle. Is null for the root "cycle". Top-level cycles point
  /// at the root.
  GenericCycle *m_parent = nullptr;

  /// The entry block(s) of the cycle. The first entry is the header.
  SmallVector<BlockType *, 1> m_entries;

  /// Child cycles, if any.
  std::vector<std::unique_ptr<GenericCycle>> m_children;

  /// Basic blocks that are contained in the cycle, including entry blocks,
  /// and including blocks that are part of a child cycle.
  std::vector<BlockType *> m_blocks;

  /// Depth of the cycle in the tree. The root "cycle" is at depth 0.
  ///
  /// \note Depths are not necessarily contiguous. However, child loops always
  ///       have strictly greater depth than their parents, and sibling loops
  ///       always have the same depth.
  unsigned m_depth = 0;

  GenericCycle(const GenericCycle &) = delete;
  GenericCycle &operator=(const GenericCycle &) = delete;
  GenericCycle(GenericCycle &&rhs) = delete;
  GenericCycle &operator=(GenericCycle &&rhs) = delete;

public:
  GenericCycle() = default;

  bool isRoot() const { return !m_parent; }

  /// \brief Whether the cycle is a natural loop.
  bool isNaturalLoop() const { return !isRoot() && m_entries.size() == 1; }

  BlockType *getHeader() const { return m_entries[0]; }

  /// \brief Return whether \p block is an entry block of the cycle.
  bool isEntry(BlockType *block) const {
    return is_contained(m_entries, block);
  }

  /// \brief Return whether \p block is contained in the cycle.
  bool containsBlock(BlockType *block) const {
    return is_contained(m_blocks, block);
  }

  const GenericCycle *getParent() const { return m_parent; }
  GenericCycle *getParent() { return m_parent; }
  uint getDepth() const { return m_depth; }

  /// Iteration over child cycles.
  //@{
  using const_child_iterator_base =
      typename std::vector<std::unique_ptr<GenericCycle>>::const_iterator;
  struct const_child_iterator
      : iterator_adaptor_base<const_child_iterator, const_child_iterator_base> {
    using Base =
        iterator_adaptor_base<const_child_iterator, const_child_iterator_base>;

    const_child_iterator() = default;
    explicit const_child_iterator(const_child_iterator_base I) : Base(I) {}

    const const_child_iterator_base& wrapped() { return Base::wrapped(); }
    GenericCycle *operator*() const { return Base::I->get(); }
  };

  const_child_iterator children_begin() const {
    return const_child_iterator{m_children.begin()};
  }
  const_child_iterator children_end() const {
    return const_child_iterator{m_children.end()};
  }
  size_t children_size() const { return m_children.size(); }
  iterator_range<const_child_iterator> children() const {
    return llvm::make_range(const_child_iterator{m_children.begin()},
                            const_child_iterator{m_children.end()});
  }
  //@}

  /// Iteration over blocks in the cycle (including entry blocks).
  //@{
  using const_blockref_iterator =
      typename std::vector<BlockType *>::const_iterator;

  size_t blocks_size() const { return m_blocks.size(); }
  iterator_range<const_blockref_iterator> blocks() const {
    return llvm::make_range(m_blocks.begin(), m_blocks.end());
  }
  //@}

  /// Iteration over entry blocks.
  //@{
  using const_entry_iterator =
      typename SmallVectorImpl<BlockType *>::const_iterator;

  size_t entries_size() const { return m_entries.size(); }
  iterator_range<const_entry_iterator> entries() const {
    return llvm::make_range(m_entries.begin(), m_entries.end());
  }

  Printable printEntries() const;
  Printable print() const;
  void dump() const { dbgs() << print(); }
};

/// \brief Type-erased cycle information for a function.
template <typename BlockType> class GenericCycleInfo {
  using Cycle = GenericCycle<BlockType>;

protected:
  /// Root "cycle".
  ///
  /// A cycle structure is used here primarily to simplify the \ref GraphTraits
  /// implementation and related iteration. Only the cycle children and entrance
  /// member is filled in, the blocks member remains empty.
  ///
  /// Top-level cycles link back to the root as their parent.
  ///
  /// A dynamic allocation is used here to allow GenericCycleInfo to be moved
  /// without invalidating any cycle pointers.
  std::unique_ptr<Cycle> m_root;

  /// Map basic blocks to their inner-most containing loop.
  DenseMap<BlockType *, Cycle *> m_blockMap;

public:
  GenericCycleInfo();
  ~GenericCycleInfo();
  GenericCycleInfo(GenericCycleInfo &&) = default;
  GenericCycleInfo &operator=(GenericCycleInfo &&) = default;

  void reset();
  void compute(BlockType *entryBlock);

  /// Methods for updating the cycle info.
  //@{
  void splitBlock(BlockType *oldBlock, BlockType *newBlock);
  void extendCycle(Cycle *cycleToExtend, BlockType *toBlock,
                   SmallVectorImpl<BlockType *> *transferredBlocks = nullptr);
  void flattenCycles(Cycle *inner, Cycle *outer);
  //@}

  /// \brief Return the root "cycle", which contains all the top-level cycles
  ///        as children.
  Cycle *getRoot() { return m_root.get(); }
  const Cycle *getRoot() const { return m_root.get(); }

  Cycle *getCycle(BlockType *block);
  const Cycle *getCycle(BlockType *block) const {
    return const_cast<GenericCycleInfo *>(this)->getCycle(block);
  }
  bool contains(const Cycle *a, const Cycle *b) const;
  Cycle *findSmallestCommonCycle(const Cycle *a, const Cycle *b);
  const Cycle *findSmallestCommonCycle(const Cycle *a, const Cycle *b) const {
    return const_cast<GenericCycleInfo *>(this)->findSmallestCommonCycle(a, b);
  };
  Cycle *findLargestDisjointAncestor(const Cycle *a, const Cycle *b);
  const Cycle *findLargestDisjointAncestor(const Cycle *a,
                                           const Cycle *b) const {
    return const_cast<GenericCycleInfo *>(this)->findLargestDisjointAncestor(a,
                                                                             b);
  }

  ArrayRef<BlockType *>
  findExitBlocks(const Cycle *cycle,
                 SmallVectorImpl<BlockType *> &tmpStorage) const;

  /// Methods for debug and self-test.
  //@{
  bool validateTree() const;
  void print(raw_ostream &out) const;
  void dump() const { print(dbgs()); }
  //@}

private:
  // Helper classes used by the cycle info computation.
  class ContractedDomSubTree;
  class Compute;

  friend struct GraphTraits<GenericCycleInfo::ContractedDomSubTree>;
  friend struct DenseMapInfo<ContractedDomSubTree>;
};

/// \brief GraphTraits for iterating over a sub-tree of the Cycle tree.
template <typename CycleRefT, typename ChildIteratorT>
struct GenericCycleGraphTraits {
  using NodeRef = CycleRefT;

  using nodes_iterator = ChildIteratorT;
  using ChildIteratorType = nodes_iterator;

  static NodeRef getEntryNode(NodeRef graph) { return graph; }

  static ChildIteratorType child_begin(NodeRef ref) {
    return ref->children_begin();
  }
  static ChildIteratorType child_end(NodeRef ref) {
    return ref->children_end();
  }

  // Not implemented:
  // static nodes_iterator nodes_begin(GraphType *G)
  // static nodes_iterator nodes_end  (GraphType *G)
  //    nodes_iterator/begin/end - Allow iteration over all nodes in the graph

  // typedef EdgeRef           - Type of Edge token in the graph, which should
  //                             be cheap to copy.
  // typedef ChildEdgeIteratorType - Type used to iterate over children edges in
  //                             graph, dereference to a EdgeRef.

  // static ChildEdgeIteratorType child_edge_begin(NodeRef)
  // static ChildEdgeIteratorType child_edge_end(NodeRef)
  //     Return iterators that point to the beginning and ending of the
  //     edge list for the given callgraph node.
  //
  // static NodeRef edge_dest(EdgeRef)
  //     Return the destination node of an edge.
  // static unsigned       size       (GraphType *G)
  //    Return total number of nodes in the graph
};

template <typename BlockType>
struct GraphTraits<const GenericCycle<BlockType> *>
    : GenericCycleGraphTraits<
          const GenericCycle<BlockType> *,
          typename GenericCycle<BlockType>::const_child_iterator> {};
template <typename BlockType>
struct GraphTraits<GenericCycle<BlockType> *>
    : GenericCycleGraphTraits<
          GenericCycle<BlockType> *,
          typename GenericCycle<BlockType>::const_child_iterator> {};

//===----------------------------------------------------------------------===//
//  Implementation details of the above templates.
//===----------------------------------------------------------------------===//
//
// Ideally, these would have been in a separate .cpp file if there was
// a common non-abstract base class for the various kinds of basic
// blocks. Due to the use of static polymorphism, this implementation
// needs to be present in a header file so that it can be instantiated
// as required. For example, see CycleInfo.cpp which instantiates the
// above templates for LLVM IR and provides a thin wrapper over it.
//
//===----------------------------------------------------------------------===//

/// \brief Helper class for computing the machine cycle information.
template <typename BlockType> class GenericCycleInfo<BlockType>::Compute {
  GenericCycleInfo &m_info;

  struct DfsInfo {
    unsigned start = 0; // DFS start; positive if block is found
    unsigned end = 0;   // DFS end

    DfsInfo() {}
    explicit DfsInfo(unsigned start) : start(start) {}

    /// Whether this node is an ancestor (or equal to) the node \p other
    /// in the DFS tree.
    bool isAncestorOf(const DfsInfo &other) const {
      return start <= other.start && other.end <= end;
    }
  };

  DenseMap<BlockType *, DfsInfo> m_blockDfsInfo;
  SmallVector<BlockType *, 8> m_blockPreorder;

  friend struct GraphTraits<ContractedDomSubTree>;

  Compute(const Compute &) = delete;
  Compute &operator=(const Compute &) = delete;

public:
  Compute(GenericCycleInfo &info) : m_info(info) {}

  void run(BlockType *entryBlock);

  static void updateDepth(GenericCycle<BlockType> *subTree);

private:
  void dfs(BlockType *entryBlock);
};

/// \brief Main function of the cycle info computations.
template <typename BlockType>
void GenericCycleInfo<BlockType>::Compute::run(BlockType *entryBlock) {
  assert(m_info.m_root->m_entries.empty());
  m_info.m_root->m_entries.push_back(entryBlock);

  dfs(entryBlock);

  SmallVector<BlockType *, 8> worklist;

  for (BlockType *headerCandidate : llvm::reverse(m_blockPreorder)) {
    const DfsInfo blockDfsInfo = m_blockDfsInfo.lookup(headerCandidate);

    for (BlockType *pred : predecessors(headerCandidate)) {
      const DfsInfo predDfsInfo = m_blockDfsInfo.lookup(pred);
      if (blockDfsInfo.isAncestorOf(predDfsInfo))
        worklist.push_back(pred);
    }
    if (worklist.empty())
      continue;

    // Found a cycle with the candidate as its header.
    std::unique_ptr<Cycle> cycle = std::make_unique<Cycle>();
    cycle->m_entries.push_back(headerCandidate);
    cycle->m_blocks.push_back(headerCandidate);
    m_info.m_blockMap.try_emplace(headerCandidate, cycle.get());

    // Helper function to process (non-back-edge) predecessors of a discovered
    // block and either add them to the worklist or recognize that the given
    // block is an additional cycle entry.
    auto processPredecessors = [&](BlockType *block) {
      bool isEntry = false;
      for (BlockType *pred : predecessors(block)) {
        const DfsInfo predDfsInfo = m_blockDfsInfo.lookup(pred);
        if (blockDfsInfo.isAncestorOf(predDfsInfo)) {
          worklist.push_back(pred);
        } else {
          isEntry = true;
        }
      }
      if (isEntry) {
        assert(!is_contained(cycle->m_entries, block));
        cycle->m_entries.push_back(block);
      }
    };

    do {
      BlockType *block = worklist.pop_back_val();
      if (block == headerCandidate)
        continue;

      auto mapIt = m_info.m_blockMap.find(block);
      if (mapIt != m_info.m_blockMap.end()) {
        // The block has already been discovered by some cycle (possibly by
        // ourself). Its outer-most discovered ancestor becomes our child if
        // that hasn't happened yet.
        Cycle *child = mapIt->second;
        while (child->m_parent)
          child = child->m_parent;
        if (child != cycle.get()) {
          auto rootIt = llvm::find_if(
              m_info.m_root->m_children,
              [=](const auto &ptr) -> bool { return child == ptr.get(); });
          assert(rootIt != m_info.m_root->m_children.end());
          cycle->m_children.push_back(std::move(*rootIt));
          *rootIt = std::move(m_info.m_root->m_children.back());
          m_info.m_root->m_children.pop_back();

          child->m_parent = cycle.get();

          cycle->m_blocks.insert(cycle->m_blocks.end(), child->m_blocks.begin(),
                                 child->m_blocks.end());

          for (BlockType *childEntry : child->entries())
            processPredecessors(childEntry);
        }
      } else {
        m_info.m_blockMap.try_emplace(block, cycle.get());
        assert(!is_contained(cycle->m_blocks, block));
        cycle->m_blocks.push_back(block);
        processPredecessors(block);
      }
    } while (!worklist.empty());

    m_info.m_root->m_children.push_back(std::move(cycle));
  }

  // Fix top-level cycle links and compute cycle depths.
  for (Cycle *topLevelCycle : m_info.m_root->children()) {
    topLevelCycle->m_parent = m_info.m_root.get();
    updateDepth(topLevelCycle);
  }
}

/// \brief Recompute depth values of \p subTree and all descendants.
template <typename BlockType>
void GenericCycleInfo<BlockType>::Compute::updateDepth(Cycle *subTree) {
  for (Cycle *cycle : depth_first(subTree))
    cycle->m_depth = cycle->m_parent->m_depth + 1;
}

/// \brief Compute a DFS of basic blocks starting at the function entry.
///
/// Fills m_blockDfsInfo with start/end counters and m_blockPreorder.
template <typename BlockType>
void GenericCycleInfo<BlockType>::Compute::dfs(BlockType *entryBlock) {
  SmallVector<unsigned, 8> dfsTreeStack;
  SmallVector<BlockType *, 8> traverseStack;
  unsigned counter = 0;
  traverseStack.emplace_back(entryBlock);

  do {
    BlockType *block = traverseStack.back();
    if (!m_blockDfsInfo.count(block)) {
      // We're visiting the block for the first time. Open its DfsInfo, add
      // successors to the traversal stack, and remember the traversal stack
      // depth at which the block was opened, so that we can correctly record
      // its end time.
      dfsTreeStack.emplace_back(traverseStack.size());
      llvm::append_range(traverseStack, successors(block));

      LLVM_ATTRIBUTE_UNUSED
      bool added = m_blockDfsInfo.try_emplace(block, ++counter).second;
      assert(added);
      m_blockPreorder.push_back(block);
    } else {
      assert(!dfsTreeStack.empty());
      if (dfsTreeStack.back() == traverseStack.size()) {
        m_blockDfsInfo.find(block)->second.end = ++counter;
        dfsTreeStack.pop_back();
      }
      traverseStack.pop_back();
    }
  } while (!traverseStack.empty());
  assert(dfsTreeStack.empty());
}

/// \brief Return printable with space-separated cycle entry blocks.
template <typename BlockType>
Printable GenericCycle<BlockType>::printEntries() const {
  return Printable([this](raw_ostream &out) {
    bool first = true;
    for (BlockType *entry : m_entries) {
      if (!first)
        out << ' ';
      first = false;
      out << entry->getName();
    }
  });
}

/// \brief Return printable representation of the cycle.
template <typename BlockType> Printable GenericCycle<BlockType>::print() const {
  return Printable([this](raw_ostream &out) {
    out << "depth=" << m_depth << ": entries(" << printEntries() << ')';

    for (BlockType *block : m_blocks) {
      if (isEntry(block))
        continue;

      out << ' ' << block->getName();
    }
  });
}

template <typename BlockType>
GenericCycleInfo<BlockType>::GenericCycleInfo()
    : m_root(std::make_unique<GenericCycle<BlockType>>()) {}
template <typename BlockType>
GenericCycleInfo<BlockType>::~GenericCycleInfo() {}

/// \brief Reset the object to its initial state.
template <typename BlockType> void GenericCycleInfo<BlockType>::reset() {
  m_root->m_entries.clear(); // remove entry block
  m_root->m_children.clear();
  m_blockMap.clear();
}

/// \brief Compute the cycle info for a function.
template <typename BlockType>
void GenericCycleInfo<BlockType>::compute(BlockType *entryBlock) {
  Compute compute(*this);
  compute.run(entryBlock);

  assert(validateTree());
}

/// \brief Update the cycle info after splitting a basic block.
///
/// Notify the cycle info that \p oldBlock was split, with \p newBlock as its
/// new unique successor. All original successors of \p oldBlock are now
/// successors of \p newBlock.
template <typename BlockType>
void GenericCycleInfo<BlockType>::splitBlock(BlockType *oldBlock,
                                             BlockType *newBlock) {
  Cycle *cycle = getCycle(oldBlock);
  if (cycle != getRoot()) {
    cycle->m_blocks.push_back(newBlock);
    m_blockMap[newBlock] = cycle;
  }
}

/// \brief Extend a cycle minimally such that it contains all predecessors of a
///        given block.
///
/// The cycle structure is updated such that all predecessors of \p toBlock will
/// be contained (possibly indirectly) in \p cycleToExtend, without removing any
/// cycles: if \p toBlock is not contained in an ancestor of \p cycle, it and
/// its ancestors will be moved into \p cycleToExtend, as will cousin cycles
/// that are encountered while following control flow backwards from \p toBlock.
///
/// If \p transferredBlocks is non-null, all blocks whose direct containing
/// cycle was changed are appended to the vector.
template <typename BlockType>
void GenericCycleInfo<BlockType>::extendCycle(
    Cycle *cycleToExtend, BlockType *toBlock,
    SmallVectorImpl<BlockType *> *transferredBlocks) {
  SmallVector<BlockType *, 32> workList;
  llvm::append_range(workList, predecessors(toBlock));

  while (!workList.empty()) {
    BlockType *block = workList.pop_back_val();
    Cycle *cycle = getCycle(block);
    if (contains(cycleToExtend, cycle))
      continue;

    Cycle *cycleToInclude = findLargestDisjointAncestor(cycle, cycleToExtend);
    if (cycleToInclude) {
      Cycle *oldCommonAncestor = cycleToInclude->getParent();

      // Move cycle into cycleToExtend.
      auto childIt = llvm::find_if(
          cycleToInclude->m_parent->m_children,
          [=](const auto &ptr) -> bool { return cycleToInclude == ptr.get(); });
      assert(childIt != cycleToInclude->m_parent->m_children.end());
      cycleToExtend->m_children.push_back(std::move(*childIt));
      *childIt = std::move(cycleToInclude->m_parent->m_children.back());
      cycleToInclude->m_parent->m_children.pop_back();
      cycleToInclude->m_parent = cycleToExtend;

      assert(cycleToInclude->m_depth <= cycleToExtend->m_depth);
      Compute::updateDepth(cycleToInclude);

      Cycle *newCommonAncestor = cycleToExtend;
      do {
        newCommonAncestor->m_blocks.insert(newCommonAncestor->m_blocks.end(),
                                           cycleToInclude->m_blocks.begin(),
                                           cycleToInclude->m_blocks.end());
        newCommonAncestor = newCommonAncestor->getParent();
      } while (newCommonAncestor != oldCommonAncestor);

      // Continue from the entries of the newly included cycle.
      for (BlockType *entry : cycleToInclude->m_entries)
        llvm::append_range(workList, predecessors(entry));
    } else {
      // Block is contained in an ancestor of cycleToExtend, just add it
      // to the cycle and proceed.
      m_blockMap[block] = cycleToExtend;
      if (transferredBlocks)
        transferredBlocks->push_back(block);

      Cycle *ancestor = cycleToExtend;
      do {
        ancestor->m_blocks.push_back(block);
        ancestor = ancestor->getParent();
      } while (ancestor != cycle);

      llvm::append_range(workList, predecessors(block));
    }
  }

  assert(validateTree());
}

/// \brief Flatten the cycle hierarchy such that \p inner is folded into
///        \p outer.
///
/// \p outer must be a strict ancestor of \p inner.
///
/// Example change to the cycle hierarchy:
///
///       outer                        outer
///      /  |                         /  |  \
///     C1  *                       C1   C2  C3
///        / \            =>
///      C2   \
///           inner
///            |
///            C3
///
template <typename BlockType>
void GenericCycleInfo<BlockType>::flattenCycles(Cycle *inner, Cycle *outer) {
  assert(outer != inner && contains(outer, inner));

  // Re-assign blocks.
  for (BlockType *block : outer->m_blocks) {
    auto it = m_blockMap.find(block);
    Cycle *cycle = inner;
    do {
      if (cycle == it->second) {
        it->second = outer;
        break;
      }
      cycle = cycle->getParent();
    } while (cycle != outer);
  }

  // Flatten the cycle hierarchy.
  do {
    // Remove the inner cycle from its direct parent.
    Cycle *parent = inner->m_parent;

    auto it = llvm::find_if(parent->m_children, [=](const auto &child) {
      return child.get() == inner;
    });
    assert(it != parent->m_children.end());

    std::unique_ptr<Cycle> innerPtr = std::move(*it);
    parent->m_children.erase(it);

    // Move the inner cycle's direct children to the outer cycle.
    for (auto &childPtr : inner->m_children) {
      childPtr->m_parent = inner->m_parent;
      outer->m_children.emplace_back(std::move(childPtr));
    }

    inner = inner->getParent();
  } while (inner != outer);

  assert(validateTree());
}

/// \brief Returns true iff \p a contains \p b.
///
/// Note: Non-strict containment check, i.e. return true if a == b.
template <typename BlockType>
bool GenericCycleInfo<BlockType>::contains(const Cycle *a,
                                           const Cycle *b) const {
  if (a->m_depth > b->m_depth)
    return false;
  while (a->m_depth < b->m_depth)
    b = b->m_parent;
  return a == b;
}

/// \brief Find the innermost cycle containing a given block.
///
/// \returns the innermost cycle containing \p block or the root "cycle" if
///          is not contained in any cycle.
template <typename BlockType>
GenericCycle<BlockType> *
GenericCycleInfo<BlockType>::getCycle(BlockType *block) {
  auto mapIt = m_blockMap.find(block);
  if (mapIt != m_blockMap.end())
    return mapIt->second;
  return m_root.get();
}

/// \brief Find the smallest cycle containing both \p a and \p b.
template <typename BlockType>
GenericCycle<BlockType> *
GenericCycleInfo<BlockType>::findSmallestCommonCycle(const Cycle *a,
                                                     const Cycle *b) {
  if (a != b) {
    for (;;) {
      while (a->m_depth > b->m_depth)
        a = a->m_parent;
      while (a->m_depth < b->m_depth)
        b = b->m_parent;
      if (a == b)
        break;
      b = b->m_parent;
      a = a->m_parent;
    }
  }
  // const_cast is justified since cycles are owned by this object, which is
  // non-const.
  return const_cast<Cycle *>(a);
}

/// \brief Finds the largest ancestor of \p a that is disjoint from \b.
///
/// The caller must ensure that \p b does not contain \p a. If \p a
/// contains \p b, null is returned.
template <typename BlockType>
GenericCycle<BlockType> *
GenericCycleInfo<BlockType>::findLargestDisjointAncestor(const Cycle *a,
                                                         const Cycle *b) {
  while (a->m_depth < b->m_depth)
    b = b->m_parent;
  if (a == b)
    return nullptr;

  for (;;) {
    while (a->m_depth > b->m_depth)
      a = a->m_parent;
    while (a->m_depth < b->m_depth)
      b = b->m_parent;
    if (a->m_parent == b->m_parent)
      break;
    a = a->m_parent;
    b = b->m_parent;
  }
  // const_cast is justified since cycles are owned by this object, which is
  // non-const.
  return const_cast<Cycle *>(a);
}

/// \brief Find (compute) the exit blocks of a given cycle
///
/// Find the blocks outside the cycle with incoming edges from the cycle.
///
/// The returned array reference remains valid as long as \p tmpStorage
/// remains unmodified.
template <typename BlockType>
ArrayRef<BlockType *> GenericCycleInfo<BlockType>::findExitBlocks(
    const Cycle *cycle, SmallVectorImpl<BlockType *> &tmpStorage) const {
  tmpStorage.clear();

  size_t numExitBlocks = 0;
  for (BlockType *block : cycle->blocks()) {
    llvm::append_range(tmpStorage, successors(block));

    for (size_t idx = numExitBlocks, end = tmpStorage.size(); idx < end;
         ++idx) {
      BlockType *succ = tmpStorage[idx];
      if (!contains(cycle, getCycle(succ))) {
        auto exitEndIt = tmpStorage.begin() + numExitBlocks;
        if (std::find(tmpStorage.begin(), exitEndIt, succ) == exitEndIt)
          tmpStorage[numExitBlocks++] = succ;
      }
    }

    tmpStorage.resize(numExitBlocks);
  }

  return tmpStorage;
}

/// \brief Validate the internal consistency of the cycle tree.
///
/// Note that this does \em not check that cycles are really cycles in the CFG,
/// or that the right set of cycles in the CFG were found.
template <typename BlockType>
bool GenericCycleInfo<BlockType>::validateTree() const {
  DenseSet<BlockType *> blocks;
  DenseSet<BlockType *> entries;

  auto reportError = [](const char *file, int line, const char *cond) {
    errs() << file << ':' << line
           << ": GenericCycleInfo::validateTree: " << cond << '\n';
  };
#define check(cond)                                                            \
  do {                                                                         \
    if (!(cond)) {                                                             \
      reportError(__FILE__, __LINE__, #cond);                                  \
      return false;                                                            \
    }                                                                          \
  } while (false)

  for (const Cycle *cycle : depth_first(getRoot())) {
    if (!cycle->m_parent) {
      check(cycle == getRoot());
      check(cycle->m_entries.size() == 1);
      check(cycle->m_blocks.empty()); // root cycle is "empty" by convention
      check(cycle->m_depth == 0);
    } else {
      check(cycle != getRoot());
      check(is_contained(cycle->m_parent->children(), cycle));

      for (BlockType *block : cycle->m_blocks) {
        auto mapIt = m_blockMap.find(block);
        check(mapIt != m_blockMap.end());
        check(contains(cycle, mapIt->second));
        check(blocks.insert(block).second); // duplicates in block list?
      }
      blocks.clear();

      check(!cycle->m_entries.empty());
      for (BlockType *entry : cycle->m_entries) {
        check(entries.insert(entry).second); // duplicate entry?
        check(is_contained(cycle->m_blocks, entry));
      }
      entries.clear();
    }

    uint childDepth = 0;
    for (const Cycle *child : cycle->children()) {
      check(child->m_depth > cycle->m_depth);
      if (!childDepth) {
        childDepth = child->m_depth;
      } else {
        check(childDepth == child->m_depth);
      }
    }
  }

  for (const auto &entry : m_blockMap) {
    BlockType *block = entry.first;
    for (const Cycle *cycle = entry.second; cycle != getRoot();
         cycle = cycle->m_parent) {
      check(is_contained(cycle->m_blocks, block));
    }
  }

#undef check

  return true;
}

/// \brief Print the cycle info.
template <typename BlockType>
void GenericCycleInfo<BlockType>::print(raw_ostream &out) const {
  for (const Cycle *cycle : depth_first(getRoot())) {
    if (!cycle->m_depth)
      continue;

    for (uint i = 0; i < cycle->m_depth; ++i)
      out << "    ";

    out << cycle->print() << '\n';
  }
}

} // namespace llvm

#endif // LLVM_GENERICCYCLEINFO_H
