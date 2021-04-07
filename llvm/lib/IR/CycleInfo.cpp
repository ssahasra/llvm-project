//===- CycleInfo.cpp - IR Cycle Info ----------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/CycleInfo.h"
#include "llvm/IR/CFG.h"
#include "llvm/Support/GenericCycleInfo.h"

using namespace llvm;

//===----------------------------------------------------------------------===//
//  Cycle Implementation
//===----------------------------------------------------------------------===//
//
// The implementation details of the wrapper class that holds a GenericCycle
// instance for LLVM IR.
//
//===----------------------------------------------------------------------===//

bool Cycle::isRoot() const { return m_cycle->isRoot(); }

/// \brief Whether the cycle is a natural loop.
bool Cycle::isNaturalLoop() const { return m_cycle->isNaturalLoop(); }

BasicBlock *Cycle::getHeader() const { return m_cycle->getHeader(); }

/// \brief Return whether \p block is an entry block of the cycle.
bool Cycle::isEntry(BasicBlock *block) const { return m_cycle->isEntry(block); }

/// \brief Return whether \p block is contained in the cycle.
bool Cycle::containsBlock(BasicBlock *block) const {
  return m_cycle->containsBlock(block);
}

const Cycle Cycle::getParent() const { return m_cycle->getParent(); }
Cycle Cycle::getParent() { return m_cycle->getParent(); }
uint Cycle::getDepth() const { return m_cycle->getDepth(); }

Cycle Cycle::const_child_iterator::operator*() const {
  return Cycle(Base::I->get());
}

Cycle::const_child_iterator Cycle::children_begin() const {
  return m_cycle->children_begin().wrapped();
}

Cycle::const_child_iterator Cycle::children_end() const {
  return m_cycle->children_end().wrapped();
}

size_t Cycle::children_size() const { return m_cycle->children_size(); }

iterator_range<Cycle::const_child_iterator> Cycle::children() const {
  return llvm::make_range(children_begin(), children_end());
}

size_t Cycle::blocks_size() const { return m_cycle->blocks_size(); }
iterator_range<Cycle::const_blockref_iterator> Cycle::blocks() const {
  return m_cycle->blocks();
}

size_t Cycle::entries_size() const { return m_cycle->entries_size(); }
iterator_range<Cycle::const_entry_iterator> Cycle::entries() const {
  return m_cycle->entries();
}

Printable Cycle::printEntries() const { return m_cycle->printEntries(); }
Printable Cycle::print() const { return m_cycle->print(); }
void Cycle::dump() const { return m_cycle->dump(); }

//===----------------------------------------------------------------------===//
//  CycleInfo Implementation
//===----------------------------------------------------------------------===//
//
// The implementation details of the wrapper class that holds a GenericCycleInfo
// instance for LLVM IR.
//
//===----------------------------------------------------------------------===//

void CycleInfo::deleter(GenericCycleInfo<BasicBlock> *ptr) {
  delete ptr;
}

CycleInfo::CycleInfo() : m_cycleinfo(new GenericCycleInfo<BasicBlock>(), deleter) {}

void CycleInfo::reset() { return m_cycleinfo->reset(); }
void CycleInfo::compute(BasicBlock *entryBlock) {
  return m_cycleinfo->compute(entryBlock);
}

/// Methods for updating the cycle info.
//@{
void CycleInfo::splitBlock(BasicBlock *oldBlock, BasicBlock *newBlock) {
  m_cycleinfo->splitBlock(oldBlock, newBlock);
}
void CycleInfo::extendCycle(Cycle cycleToExtend, BasicBlock *toBlock,
                            SmallVectorImpl<BasicBlock *> *transferredBlocks) {
  return m_cycleinfo->extendCycle(cycleToExtend.m_cycle, toBlock,
                                  transferredBlocks);
}
void CycleInfo::flattenCycles(Cycle inner, Cycle outer) {
  return m_cycleinfo->flattenCycles(inner.m_cycle, outer.m_cycle);
}
//@}

/// \brief Return the root "cycle", which contains all the top-level cycles
///        as children.
Cycle CycleInfo::getRoot() { return Cycle(m_cycleinfo->getRoot()); }
const Cycle CycleInfo::getRoot() const {
  return const_cast<CycleInfo *>(this)->getRoot();
}

Cycle CycleInfo::getCycle(BasicBlock *block) {
  return Cycle(m_cycleinfo->getCycle(block));
}
const Cycle CycleInfo::getCycle(BasicBlock *block) const {
  return Cycle(m_cycleinfo->getCycle(block));
}
bool CycleInfo::contains(const Cycle a, const Cycle b) const {
  return m_cycleinfo->contains(a.m_cycle, b.m_cycle);
}
Cycle CycleInfo::findSmallestCommonCycle(const Cycle a, const Cycle b) {
  return Cycle(m_cycleinfo->findSmallestCommonCycle(a.m_cycle, b.m_cycle));
}
const Cycle CycleInfo::findSmallestCommonCycle(const Cycle a,
                                               const Cycle b) const {
  return const_cast<CycleInfo *>(this)->findSmallestCommonCycle(a, b);
}
Cycle CycleInfo::findLargestDisjointAncestor(const Cycle a, const Cycle b) {
  return m_cycleinfo->findLargestDisjointAncestor(a.m_cycle, b.m_cycle);
}
const Cycle CycleInfo::findLargestDisjointAncestor(const Cycle a,
                                                   const Cycle b) const {
  return const_cast<CycleInfo *>(this)->findLargestDisjointAncestor(a, b);
}

ArrayRef<BasicBlock *>
CycleInfo::findExitBlocks(const Cycle cycle,
                          SmallVectorImpl<BasicBlock *> &tmpStorage) const {
  return m_cycleinfo->findExitBlocks(cycle.m_cycle, tmpStorage);
}

/// Methods for debug and self-test.
//@{
bool CycleInfo::validateTree() const { return m_cycleinfo->validateTree(); }
void CycleInfo::print(raw_ostream &out) const {
  return m_cycleinfo->print(out);
}
//@}
