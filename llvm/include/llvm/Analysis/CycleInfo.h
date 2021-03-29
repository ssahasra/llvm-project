//===- CycleInfo.h - IR Cycle Info ------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines the CycleInfo class, which is a thin wrapper over
// the LLVM IR instance of GenericCycleInfo.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_IR_CYCLEINFO_H
#define LLVM_IR_CYCLEINFO_H

#include "llvm/IR/PassManager.h"
#include "llvm/Support/Printable.h"

namespace llvm {
class BasicBlock;
template <typename BlockType> class GenericCycle;

class CycleInfo;

/// A simple wrapper that contains a pointer to an LLVM IR instance of
/// GenericCycle. All methods are forwarded to GenericCycle via the
/// pointer. Objects of class Cycle are always passed around by value.
class Cycle {
  GenericCycle<BasicBlock> *m_cycle;
  friend class CycleInfo;

public:
  Cycle(GenericCycle<BasicBlock> *C) : m_cycle(C) {}
  bool isRoot() const;

  /// \brief Whether the cycle is a natural loop.
  bool isNaturalLoop() const;

  BasicBlock *getHeader() const;

  /// \brief Return whether \p block is an entry block of the cycle.
  bool isEntry(BasicBlock *block) const;

  /// \brief Return whether \p block is contained in the cycle.
  bool containsBlock(BasicBlock *block) const;

  const Cycle getParent() const;
  Cycle getParent();
  uint getDepth() const;

  /// Iteration over child cycles.
  //@{
  using const_child_iterator_base =
    typename std::vector<std::unique_ptr<GenericCycle<BasicBlock>>>::const_iterator;
  struct const_child_iterator
      : iterator_adaptor_base<const_child_iterator, const_child_iterator_base> {
    using Base =
        iterator_adaptor_base<const_child_iterator, const_child_iterator_base>;

    Cycle operator *() const;
    const_child_iterator(const_child_iterator_base I) : Base(I) {}
  };

  const_child_iterator children_begin() const;
  const_child_iterator children_end() const;
  size_t children_size() const;
  iterator_range<const_child_iterator> children() const;

  /// Iteration over blocks in the cycle (including entry blocks).
  //@{
  using const_blockref_iterator =
      typename std::vector<BasicBlock *>::const_iterator;

  size_t blocks_size() const;
  iterator_range<const_blockref_iterator> blocks() const;
  //@}

  /// Iteration over entry blocks.
  //@{
  using const_entry_iterator =
      typename SmallVectorImpl<BasicBlock *>::const_iterator;

  size_t entries_size() const;
  iterator_range<const_entry_iterator> entries() const;
  //@}

  Printable printEntries() const;
  Printable print() const;
  void dump() const;
};

template <typename BlockType> class GenericCycleInfo;
class CycleInfo {
  struct Deleter {
    void operator()(GenericCycleInfo<BasicBlock> *ptr);
  };
  std::unique_ptr<GenericCycleInfo<BasicBlock>, Deleter> m_cycleinfo;

public:
  CycleInfo();
  void reset();
  void compute(BasicBlock *entryBlock);

  /// Methods for updating the cycle info.
  //@{
  void splitBlock(BasicBlock *oldBlock, BasicBlock *newBlock);
  void extendCycle(Cycle cycleToExtend, BasicBlock *toBlock,
                   SmallVectorImpl<BasicBlock *> *transferredBlocks = nullptr);
  void flattenCycles(Cycle inner, Cycle outer);
  //@}

  /// \brief Return the root "cycle", which contains all the top-level cycles
  ///        as children.
  Cycle getRoot();
  const Cycle getRoot() const;

  Cycle getCycle(BasicBlock *block);
  const Cycle getCycle(BasicBlock *block) const;
  bool contains(const Cycle a, const Cycle b) const;
  Cycle findSmallestCommonCycle(const Cycle a, const Cycle b);
  const Cycle findSmallestCommonCycle(const Cycle a, const Cycle b) const;
  Cycle findLargestDisjointAncestor(const Cycle a, const Cycle b);
  const Cycle findLargestDisjointAncestor(const Cycle a, const Cycle b) const;

  ArrayRef<BasicBlock *>
  findExitBlocks(const Cycle cycle,
                 SmallVectorImpl<BasicBlock *> &tmpStorage) const;

  /// Methods for debug and self-test.
  //@{
  bool validateTree() const;
  void print(raw_ostream &out) const;
  void dump() const { print(dbgs()); }
  //@}
};

/// Analysis pass which computes a \ref CycleInfo.
class CycleInfoAnalysis : public AnalysisInfoMixin<CycleInfoAnalysis> {
  friend AnalysisInfoMixin<CycleInfoAnalysis>;
  static AnalysisKey Key;

public:
  /// Provide the result typedef for this analysis pass.
  using Result = CycleInfo;

  /// Run the analysis pass over a function and produce a dominator tree.
  CycleInfo run(Function &F, FunctionAnalysisManager &);

  // TODO: verify analysis?
};

/// Printer pass for the \c DominatorTree.
class CycleInfoPrinterPass : public PassInfoMixin<CycleInfoPrinterPass> {
  raw_ostream &OS;

public:
  explicit CycleInfoPrinterPass(raw_ostream &OS);

  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

/// Legacy analysis pass which computes a \ref CycleInfo.
class CycleInfoWrapperPass : public FunctionPass {
  Function *m_function = nullptr;
  CycleInfo m_cycleInfo;

public:
  static char ID;

  CycleInfoWrapperPass();

  CycleInfo &getCycleInfo() { return m_cycleInfo; }
  const CycleInfo &getCycleInfo() const { return m_cycleInfo; }

  bool runOnFunction(Function &F) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  void releaseMemory() override;
  void print(raw_ostream &OS, const Module *M = nullptr) const override;

  // TODO: verify analysis?
};

} // end namespace llvm

#endif // LLVM_ANALYSIS_CYCLEINFO_H
