/******************************************************************************
 * Top contributors (to current version):
 *   anynomous author
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Optimizer for Non-linear Real type.
 */

#ifndef CVC5__OMT__MCSAT_OPTIMIZER_H
#define CVC5__OMT__MCSAT_OPTIMIZER_H

#include "omt/omt_optimizer.h"
#include "smt/solver_engine.h"

namespace cvc5::internal::omt {

/**
 * Optimizer for Integer type
 */
class OMTOptimizerMCSAT : public OMTOptimizer
{
 public:
  OMTOptimizerMCSAT() = default;
  virtual ~OMTOptimizerMCSAT() = default;
  smt::OptimizationResult minimize(SolverEngine* optChecker,
                                   TNode target) override;
  smt::OptimizationResult maximize(SolverEngine* optChecker,
                                   TNode target) override;

  virtual std::unique_ptr<SolverEngine> createOptPreChecker(SolverEngine* parentSMTSolver);
//   virtual void phase_reconstruct();
  
 private:
  /**
   * Handles the optimization query specified by objType
   * isMinimize = true will trigger minimization,
   * otherwise trigger maximization
   **/
  smt::OptimizationResult optimize(SolverEngine* optChecker,
                                   TNode target,
                                   bool isMinimize);

      /** A subsolver for offline optimization **/
      std::unique_ptr<SolverEngine> d_optPreChecker;
};

}  // namespace cvc5::internal::omt

#endif /* CVC5__OMT__MCSAT_OPTIMIZER_H */
