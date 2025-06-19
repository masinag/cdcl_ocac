/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements the CDCAC approach as described in
 * https://arxiv.org/pdf/2003.05633.pdf.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__COVERINGS__CDCAC_H
#define CVC5__THEORY__ARITH__NL__COVERINGS__CDCAC_H

#ifdef CVC5_POLY_IMP

#include <poly/polyxx.h>

#include <vector>

#include "smt/env.h"
#include "smt/env_obj.h"
#include "theory/arith/nl/coverings/cdcac_utils.h"
#include "theory/arith/nl/coverings/constraints.h"
#include "theory/arith/nl/coverings/lazard_evaluation.h"
#include "theory/arith/nl/coverings/proof_generator.h"
#include "theory/arith/nl/coverings/variable_ordering.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

class NlModel;

namespace coverings {

class objectiveValue{
public:
  enum class OPT_VALUE_TYPE{
    MINUS_EPSILON = 0,
    PLUS_EPSILON = 50,
    EXACT = 100
  };
  Node objective;
  poly::Variable objVar;
  bool _isSAT = false;
  bool _isCurSAT = false;
  OPT_TYPE _isOptimization = OPT_TYPE::NON_OPT;
  std::vector<CACInterval> infeasibleIntervals;
  // current assignment in current branch
  poly::Assignment curAssignment;
  poly::Value curModelValue;
  poly::Value curBoundValue;
  OPT_VALUE_TYPE curOptimizedValue;
  void setCurModelValue(const poly::Value& val);
  void setCurAssignment(const poly::Variable &var, const poly::Value& val);
  // optimized assignment in total branches
  bool first = true;
  poly::Assignment optAssignment;
  poly::Value optModelValue;
  poly::Value optBoundValue;
  OPT_VALUE_TYPE optOptimizedValue;
  void setOptAssignment(const poly::Variable &var, const poly::Value& val);
  // poly::Value modelValue;
  // poly::Value boundValue;
  // OPT_VALUE_TYPE optimizedValue;
  objectiveValue(){}
  ~objectiveValue(){}
  void setObjective(OPT_TYPE _isOpt, Node& e);
  void setInfeasibleIntervals(const std::vector<CACInterval>& infs);
  void analyzeInfeasibleIntervals();
  void setSAT();
  void setCurSAT();
  void unsetCurSAT();
  bool isSAT() const; // globally found satisfiability 
  bool isCurSAT() const; // found satisfiability in current branch
  void assertOptBound();
  Node getBoundValue() const;
  Node getOptimizedValue() const;
  Node getOptimizedAssignment(const poly::Variable& pvar, const Node& var) const;
  bool missBound() const;
  const poly::Assignment& getModel() const;

  // value to node conversion
  Node obj_value_to_node(const poly::Value &v, const Node& var) const;

  // make incremental lemma
  bool isMax() const;
  bool isMin() const;
  Node mkIncrementLemma();

  // make unsat opt assignment lemma
  Node objCurVal;
  Node mkUnsatOptLemma();
  
  // unbounded
  bool _isApprox = false;
  bool _isPosInf = false;
  bool _isPosApprox = false;
  bool _isUnbounded = false;
  void reset();
  bool isUnbounded() const;
  bool isApprox() const;
  bool isPosInf() const;
  bool isNegInf() const;
  bool isPosApprox() const;
  bool isNegApprox() const;
  void setPosUnbounded();
  void setNegUnbounded();
  void setPosApprox();
  void setNegApprox();
  bool maybeUnbounded = false;
  poly::Interval unboundedProof;
  poly::Value optApproxValue;

  // making unsat flag
  bool _removing_sat_assignment = false;
  void set_removing_sat_assignment();
  void unset_removing_sat_assignment();
  bool is_removing_sat_assignment() const;

  // analyze cell
  std::vector<poly::Interval> feasibles;
  void analyze_cell(const CACInterval& characterization, const std::vector<CACInterval>& infeasibles);

  // 2023-12-04: optimization save roots for sat cells
  bool has_computed_roots = false;
  std::vector<poly::Value> roots;
  std::vector<poly::Interval> roots_intervals;
};

/**
 * This class implements Cylindrical Algebraic Coverings as presented in
 * https://arxiv.org/pdf/2003.05633.pdf
 */
class CDCAC : protected EnvObj
{
 public:
  /** Initialize this method with the given variable ordering. */
  CDCAC(Env& env, const std::vector<poly::Variable>& ordering = {});

  /** Reset this instance. */
  void reset();

  /** Collect variables from the constraints and compute a variable ordering. */
  void computeVariableOrdering();

  /**
   * Extract an initial assignment from the given model.
   * This initial assignment is used to guide sampling if possible.
   * The ran_variable should be the variable used to encode real algebraic
   * numbers in the model and is simply passed on to node_to_value.
   */
  void retrieveInitialAssignment(NlModel& model, const Node& ran_variable);

  /**
   * Returns the constraints as a non-const reference. Can be used to add new
   * constraints.
   */
  Constraints& getConstraints();
  /** Returns the constraints as a const reference. */
  const Constraints& getConstraints() const;

  /**
   * Returns the current assignment. This is a satisfying model if
   * get_unsat_cover() returned an empty vector.
   */
  const poly::Assignment& getModel() const;

  /** Returns the current variable ordering. */
  const std::vector<poly::Variable>& getVariableOrdering() const;

  /**
   * Collect all unsatisfiable intervals for the given variable.
   * Combines unsatisfiable regions from d_constraints evaluated over
   * d_assignment. Implements Algorithm 2.
   */
  std::vector<CACInterval> getUnsatIntervals(std::size_t cur_variable);

  /**
   * Sample outside of the set of intervals.
   * Uses a given initial value from mInitialAssignment if possible.
   * Returns whether a sample was found (true) or the infeasible intervals cover
   * the whole real line (false).
   */
  bool sampleOutsideWithInitial(const std::vector<CACInterval>& infeasible,
                                poly::Value& sample,
                                std::size_t cur_variable);

  /**
   * Collects the coefficients required for projection from the given
   * polynomial. Implements Algorithm 6, depending on the command line
   * arguments. Either directly implements Algorithm 6, or improved variants
   * based on Lazard's projection.
   */
  PolyVector requiredCoefficients(const poly::Polynomial& p);

  /**
   * Constructs a characterization of the given covering.
   * A characterization contains polynomials whose roots bound the region around
   * the current assignment. Implements Algorithm 4.
   */
  PolyVector constructCharacterization(std::vector<CACInterval>& intervals);

  /**
   * Constructs an infeasible interval from a characterization.
   * Implements Algorithm 5.
   */
  CACInterval intervalFromCharacterization(const PolyVector& characterization,
                                           std::size_t cur_variable,
                                           const poly::Value& sample);
  CACInterval intervalFromSATCharacterization(const PolyVector& characterization,
                                           std::size_t cur_variable,
                                           const poly::Value& sample);

  /**
   * Internal implementation of getUnsatCover().
   * @param curVariable The id of the variable (within d_variableOrdering) to
   * be considered. This argument is used to manage the recursion internally and
   * should always be zero if called externally.
   * @param returnFirstInterval If true, the function returns after the first
   * interval obtained from a recursive call. The result is not (necessarily) an
   * unsat cover, but merely a list of infeasible intervals.
   */
  std::vector<CACInterval> getUnsatCoverImpl(std::size_t curVariable = 0,
                                             bool returnFirstInterval = false);

  /**
   * Main method that checks for the satisfiability of the constraints.
   * Recursively explores possible assignments and excludes regions based on the
   * coverings. Returns either a covering for the lowest dimension or an empty
   * vector. If the covering is empty, the result is SAT and an assignment can
   * be obtained from d_assignment. If the covering is not empty, the result is
   * UNSAT and an infeasible subset can be extracted from the returned covering.
   * Implements Algorithm 2.
   * This method itself only takes care of the outermost proof scope and calls
   * out to getUnsatCoverImpl() with curVariable set to zero.
   * @param returnFirstInterval If true, the function returns after the first
   * interval obtained from a recursive call. The result is not (necessarily) an
   * unsat cover, but merely a list of infeasible intervals.
   */
  std::vector<CACInterval> getUnsatCover(bool returnFirstInterval = false);

  void startNewProof();
  /**
   * Finish the generated proof (if proofs are enabled) with a scope over the
   * given assertions.
   */
  ProofGenerator* closeProof(const std::vector<Node>& assertions);

  /** Get the proof generator */
  CoveringsProofGenerator* getProof() { return d_proof.get(); }

  // anynomous author: optimization
  OPT_TYPE _isOptimization = OPT_TYPE::NON_OPT;
  bool isOptSAT() const;
  bool isCurSAT() const;
  void setOptimization();
  void setObjective(OPT_TYPE _isOpt, Node& e);
  bool isOptimization() const;
  Node objectiveVariable;
  size_t objectiveIndex = 0;
  void assertOptBound();
  void setCurAssignment();
  bool missBound() const;
  Node getBoundValue(const Node& e) const;
  Node getOptimizedValue(const Node& e) const;

  // anynomous author: optimization: inner functions
  bool sampleSAT = false; // anynomous author: it is a satisfiability track in the sample process 
  objectiveValue objValue;
  std::vector<CACInterval> getSatIntervals(std::size_t cur_variable);
  CACInterval optimizedInterval(const poly::Value& sample);
  void setOptValues();
  void getOptModelCache(std::map<Node, Node>& optCache);
  bool isOptUnbounded() const;
  bool isOptPosInf() const;
  bool isOptNegInf() const;
  bool isOptPosApprox() const; // a + \epsilon
  bool isOptNegApprox() const;

  // anynomous author: check polynomial
  void get_coefficients(const Node& p, std::vector<poly::Value>& coes);
  bool check_normal_polynomials(const std::vector<Node>& origins);

 private:
  /** Check whether proofs are enabled */
  bool isProofEnabled() const { return d_proof != nullptr; }

  /**
   * Check whether the current sample satisfies the integrality condition of the
   * current variable. Returns true if the variable is not integral or the
   * sample is integral.
   */
  bool checkIntegrality(std::size_t cur_variable, const poly::Value& value);
  /**
   * Constructs an interval that excludes the non-integral region around the
   * current sample. Assumes !check_integrality(cur_variable, value).
   */
  CACInterval buildIntegralityInterval(std::size_t cur_variable,
                                       const poly::Value& value);

  /**
   * Check whether the polynomial has a real root above the given value (when
   * evaluated over the current assignment).
   */
  bool hasRootAbove(const poly::Polynomial& p, const poly::Value& val) const;
  /**
   * Check whether the polynomial has a real root below the given value (when
   * evaluated over the current assignment).
   */
  bool hasRootBelow(const poly::Polynomial& p, const poly::Value& val) const;

  /**
   * Sort intervals according to section 4.4.1. and removes fully redundant
   * intervals as in 4.5. 1. by calling out to cleanIntervals.
   * Additionally makes sure to prune proofs for removed intervals.
   */
  void pruneRedundantIntervals(std::vector<CACInterval>& intervals);

  /**
   * Prepare the lazard evaluation object with the current assignment, if the
   * lazard lifting is enabled. Otherwise, this function does nothing.
   */
  void prepareRootIsolation(LazardEvaluation& le, size_t cur_variable) const;

  /**
   * Isolates the real roots of the polynomial `p`. If the lazard lifting is
   * enabled, this function uses `le.isolateRealRoots()`, otherwise uses the
   * regular `poly::isolate_real_roots()`.
   */
  std::vector<poly::Value> isolateRealRoots(LazardEvaluation& le,
                                            const poly::Polynomial& p) const;

  /**
   * The current assignment. When the method terminates with SAT, it contains a
   * model for the input constraints.
   */
  poly::Assignment d_assignment;

  /** The set of input constraints to be checked for consistency. */
  Constraints d_constraints;

  /** The computed variable ordering used for this method. */
  std::vector<poly::Variable> d_variableOrdering;

  /** The object computing the variable ordering. */
  VariableOrdering d_varOrder;

  /** The linear assignment used as an initial guess. */
  std::vector<poly::Value> d_initialAssignment;

  /** The proof generator */
  std::unique_ptr<CoveringsProofGenerator> d_proof;

  /** The next interval id */
  size_t d_nextIntervalId = 1;
};

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif

#endif
