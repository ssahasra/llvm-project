//===- CycleConvergenceExtend.cpp - Extend cycle body for convergence -----===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements a pass to convert all uncontrolled convergent operations
// into controlled convergent operations, using the following heuristic:
//
// 1. If an irreducible cycle contains a convergent operation, convert it into a
//    reducible cycle (natural loop).
//
// 2. Insert a call to convergence.entry at the start of the entry block of the
//    function.
//
// 3. Insert a call to llvm.experimental.convergence.loop at the start of every
//    loop header. If this loop is an outermost loop, the convergencectrl
//    operand is the call to llvm.experimental.convergence.entry in the entry
//    block of the function. Otherwise, the convergencectrl operand is the call
//    to llvm.experimental.convergence.loop in the parent loop's header.
//
// 4. For each uncontrolled convergent operation X, add a convergencectrl
//    operand bundle using the token defined by a definition D that is a sibling
//    to this operation. D always dominates X: if X is not in any cycle, then D
//    is a call to llvm.experimental.convergence.entry; otherwise D is the heart
//    of the parent cycle of X.
//
// NOTE: For best results, before running this pass, an attempt should be made
// to remove the convergent attribute either using a FunctionAttrs pass or the
// Attributor pass.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/AddConvergenceControl.h"
#include "llvm/Analysis/CycleAnalysis.h"
#include "llvm/Analysis/DomTreeUpdater.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/Utils/FixIrreducible.h"

#define DEBUG_TYPE "add-convergence-control"

using namespace llvm;

using CycleHeartMap = DenseMap<Cycle *, CallInst *>;

static void insertEntryToken(Function &F, CycleHeartMap &HeartMap) {
  F.setConvergent();
  BasicBlock::iterator InsertPt = F.getEntryBlock().getFirstInsertionPt();
  Function *LoopIntrinsic = Intrinsic::getDeclaration(F.getParent(), Intrinsic::experimental_convergence_entry);
  CallInst *EntryToken = CallInst::Create(LoopIntrinsic, "", InsertPt);
  auto Result = HeartMap.insert_or_assign(nullptr, EntryToken);
  assert(Result.second);
}

static void insertCycleHeart(Cycle &C, CycleHeartMap &HeartMap, Module &M) {
  BasicBlock *Header = C.getHeader();
  CallInst *ParentToken = HeartMap.lookup(C.getParentCycle());
  assert(ParentToken);
  BasicBlock::iterator InsertPt = Header->getFirstInsertionPt();
  Function *LoopIntrinsic = Intrinsic::getDeclaration(&M, Intrinsic::experimental_convergence_loop);
  OperandBundleDef TokenOp("convergencectrl", ParentToken);
  CallInst *Heart = CallInst::Create(LoopIntrinsic, {}, TokenOp, "", InsertPt);
  auto Result = HeartMap.insert_or_assign(&C, Heart);
  assert(Result.second);
  dbgs() << "Added heart for cyle: ";
  C.getHeader()->printAsOperand(dbgs());
  dbgs() << "\n";
}

PreservedAnalyses AddConvergenceControlPass::run(Function &F, FunctionAnalysisManager &AM) {
  LLVM_DEBUG(dbgs() << "=== Adding convergence control in function " << F.getName() << "\n");

  auto *LI = AM.getCachedResult<LoopAnalysis>(F);
  auto &CI = AM.getResult<CycleAnalysis>(F);
  auto &DT = AM.getResult<DominatorTreeAnalysis>(F);

  SmallVector<Cycle*> Cycles;
  SmallVector<CallBase*> ConvOps;
  for (Instruction &I : instructions(F)) {
    if (auto *CB = dyn_cast<CallBase>(&I)) {
      if (!CB->isConvergent())
        continue;
      // The reasonable expectation is that if tokens are used anywhere in the
      // module, then there are no uncontrolled convergent operations.
      if (CB->getConvergenceControlToken() || isa<ConvergenceControlInst>(CB)) {
        assert(Cycles.empty());
        assert(ConvOps.empty());
        return PreservedAnalyses::all();
      }

      ConvOps.push_back(CB);

      Cycle *C = CI.getCycle(CB->getParent());
      while (C) {
        Cycles.push_back(C);
        C = C->getParentCycle();
      }
    }
  }

  // Make a set out of the vector.
  llvm::sort(Cycles);
  auto Last = llvm::unique(Cycles);
  Cycles.erase(Last, Cycles.end());

  // We can't work with irreducible cycles.
  for (Cycle *C : Cycles) {
    if (!C->isReducible())
      fixIrreducibleCycle(*C, CI, DT, LI);
  }

  // Sort by order of increasing depth. This ensures that we add tokens to a
  // parent cycle before its children.
  llvm::sort(Cycles, [](const Cycle *A, const Cycle *B) {
    return A->getDepth() < B->getDepth();
  });

  CycleHeartMap CycleHearts{(unsigned)Cycles.size()};
  insertEntryToken(F, CycleHearts);
  for (Cycle *C : Cycles) {
    insertCycleHeart(*C, CycleHearts, *F.getParent());
  }

  for (CallBase *CB : ConvOps) {
    CB->dump();
    Cycle *C = CI.getCycle(CB->getParent());
    dbgs() << "Find heart for cyle: ";
    if (C)
      C->getHeader()->printAsOperand(dbgs());
    else
      dbgs() << "top-level";
    dbgs() << "\n";
    CallInst *ControlToken = CycleHearts.lookup(C);
    assert(ControlToken);
    OperandBundleDef TokenBundle("convergencectrl", ControlToken);
    CallBase *NewCB = CallBase::addOperandBundle(CB, LLVMContext::OB_convergencectrl, TokenBundle, CB);
    CB->replaceAllUsesWith(NewCB);
    CB->eraseFromParent();
  }

  return PreservedAnalyses::all();
}
