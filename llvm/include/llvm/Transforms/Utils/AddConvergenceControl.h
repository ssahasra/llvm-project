//===- AddConvergenceControl.h - Extend cycles for convergence -*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file provides the interface for the AddConvergenceControl pass.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_UTILS_ADDCONVERGENCECONTROL_H
#define LLVM_TRANSFORMS_UTILS_ADDCONVERGENCECONTROL_H

#include "llvm/IR/PassManager.h"

namespace llvm {

class AddConvergenceControlPass
    : public PassInfoMixin<AddConvergenceControlPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // end namespace llvm

#endif // LLVM_TRANSFORMS_UTILS_ADDCONVERGENCECONTROL_H
