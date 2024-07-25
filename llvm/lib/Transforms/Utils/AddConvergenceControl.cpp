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
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"

#define DEBUG_TYPE "add-convergence-control"

using namespace llvm;

PreservedAnalyses AddConvergenceControlPass::run(Module &M,
                                                  ModuleAnalysisManager &MAM) {
  LLVM_DEBUG(dbgs() << "=== Adding convergence control\n");

  for (Function &F : M) {
    LLVM_DEBUG(dbgs() << "=== Inspecting function " << F.getName() << "\n");
    for (Instruction *I : instructions(F)) {
      if (auto *CB = dyn_cast<CallBase>(I)) {
        if (!CB->isConvergent())
          continue;
      }
    }
  }
}
