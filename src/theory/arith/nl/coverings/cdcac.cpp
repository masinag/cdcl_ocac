/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Mathias Preiner
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

#include "theory/arith/nl/coverings/cdcac.h"

#ifdef CVC5_POLY_IMP

#include "options/arith_options.h"
#include "theory/arith/nl/coverings/lazard_evaluation.h"
#include "theory/arith/nl/coverings/projections.h"
#include "theory/arith/nl/coverings/variable_ordering.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/resource_manager.h"

using namespace cvc5::internal::kind;

namespace std {
/** Generic streaming operator for std::vector. */
template <typename T>
std::ostream& operator<<(std::ostream& os, const std::vector<T>& v)
{
  cvc5::internal::container_to_stream(os, v);
  return os;
}
}  // namespace std

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace coverings {

CDCAC::CDCAC(Env& env, const std::vector<poly::Variable>& ordering)
    : EnvObj(env), d_variableOrdering(ordering)
{
  if (d_env.isTheoryProofProducing())
  {
    d_proof.reset(new CoveringsProofGenerator(env, userContext()));
  }
}

void CDCAC::reset()
{
  d_constraints.reset();
  d_assignment.clear();
  d_nextIntervalId = 1;
}

void CDCAC::computeVariableOrdering()
{
  // anynomous author: Compute variable order, invoke our optimization variable order.
  //      so we pass d_constraints as parameter for d_constraints.varMapper()()
  // Actually compute the variable ordering
  if(isOptimization()){
    // anynomous author: the first variable will be projected first.
    //      [x, y, z] -> first sample x, then y, and finally z.
    d_variableOrdering = d_varOrder(d_constraints,
                                    VariableOrderingStrategy::OPT_SIMP);
    objectiveIndex = 0;
    objValue.objVar = d_variableOrdering[objectiveIndex];
  }
  else{
    d_variableOrdering = d_varOrder(d_constraints,
                                    VariableOrderingStrategy::BROWN);
  }
  
  Trace("cdcac") << "Variable ordering is now " << d_variableOrdering
                 << std::endl;

  // Write variable ordering back to libpoly.
  lp_variable_order_t* vo = poly::Context::get_context().get_variable_order();
  lp_variable_order_clear(vo);
  for (const auto& v : d_variableOrdering)
  {
    lp_variable_order_push(vo, v.get_internal());
  }
}

void CDCAC::retrieveInitialAssignment(NlModel& model, const Node& ran_variable)
{
  if (options().arith.nlCovLinearModel == options::nlCovLinearModelMode::NONE) return;
  d_initialAssignment.clear();
  Trace("cdcac") << "Retrieving initial assignment:" << std::endl;
  for (const auto& var : d_variableOrdering)
  {
    Node v = getConstraints().varMapper()(var);
    Node val = model.computeConcreteModelValue(v);
    poly::Value value = node_to_value(val, ran_variable);
    Trace("cdcac") << "\t" << var << " = " << value << std::endl;
    d_initialAssignment.emplace_back(value);
  }
}
Constraints& CDCAC::getConstraints() { return d_constraints; }
const Constraints& CDCAC::getConstraints() const { return d_constraints; }

const poly::Assignment& CDCAC::getModel() const {
  if(isOptimization()){
    return objValue.getModel();
  }
  else return d_assignment; 
}

const std::vector<poly::Variable>& CDCAC::getVariableOrdering() const
{
  return d_variableOrdering;
}

std::vector<CACInterval> CDCAC::getUnsatIntervals(std::size_t cur_variable)
{
  std::vector<CACInterval> res;
  LazardEvaluation le(statisticsRegistry());
  prepareRootIsolation(le, cur_variable);
  for (const auto& c : d_constraints.getConstraints())
  {
    const poly::Polynomial& p = std::get<0>(c);
    poly::SignCondition sc = std::get<1>(c);
    const Node& n = std::get<2>(c);

    if (main_variable(p) != d_variableOrdering[cur_variable])
    {
      // Constraint is in another variable, ignore it.
      continue;
    }

    Trace("cdcac") << "Infeasible intervals for " << p << " " << sc
                   << " 0 over " << d_assignment << std::endl;
    std::vector<poly::Interval> intervals;
    if (options().arith.nlCovLifting
        == options::nlCovLiftingMode::LAZARD)
    {
      intervals = le.infeasibleRegions(p, sc);
      if (TraceIsOn("cdcac"))
      {
        auto reference = poly::infeasible_regions(p, d_assignment, sc);
        Trace("cdcac") << "Lazard: " << intervals << std::endl;
        Trace("cdcac") << "Regular: " << reference << std::endl;
      }
    }
    else
    {
      intervals = poly::infeasible_regions(p, d_assignment, sc);
    }
    for (const auto& i : intervals)
    {
      Trace("cdcac") << "-> " << i << std::endl;
      PolyVector l, u, m, d;
      m.add(p);
      m.pushDownPolys(d, d_variableOrdering[cur_variable]);
      if (!is_minus_infinity(get_lower(i))) l = m;
      if (!is_plus_infinity(get_upper(i))) u = m;
      res.emplace_back(CACInterval{d_nextIntervalId++, i, l, u, m, d, {n}});
      if (isProofEnabled())
      {
        d_proof->addDirect(
            d_constraints.varMapper()(d_variableOrdering[cur_variable]),
            d_constraints.varMapper(),
            p,
            d_assignment,
            sc,
            i,
            n,
            res.back().d_id);
      }
    }
  }
  pruneRedundantIntervals(res);
  return res;
}

bool CDCAC::sampleOutsideWithInitial(const std::vector<CACInterval>& infeasible,
                                     poly::Value& sample,
                                     std::size_t cur_variable)
{
  if(isOptimization() && cur_variable == objectiveIndex){
    // // if current sat -> return with direction
    // if(objValue.isCurSAT()) return sampleOutsidewithDirection(infeasible, sample, _isOptimization == OPT_TYPE::MINIMIZATION);
    // // else current branch unsat -> return only sample outside
    // else return sampleOutside(infeasible, sample);
    // anynomous author: 2023-08-16: it only affects efficiency, so sampleOutsidewithDirection is alright
    //      but sampleOutside will result in an error in optimization mode.
    //      For example, (-oo, 3/2) with min -> sampleOutside samples between [3/2, +oo);
    //      while sampleOutsidewithDirection samples 3/2.
    
    // std::vector<poly::Interval> infs;
    // for(size_t i=0;i<infeasible.size();i++){
    //   infs.emplace_back(infeasible[i].d_interval);
    // }
    // auto feasible = intervalMinus(poly::Interval().full(), infs);
    // for(size_t i=0;i<objValue.roots_intervals.size();i++){
    //   Trace("cdcac") << "Checking " << objValue.roots_intervals[i] << " against " << feasible.front() << std::endl;
    //   auto itv = intervalIntersect(objValue.roots_intervals[i], feasible);
    //   // sample = poly::pick_value(itv.front());
    //   // return true;
    //   // // anynomous author: can optimize to shrink
    //   // if (itv.empty()) continue;
    //   // else{
    //   //   auto flip_intervals = intervalMinus(poly::Interval().full(), itv);
    //   //   std::vector<CACInterval> new_filp_intervals;
    //   //   for(size_t j=0;j<flip_intervals.size();j++){
    //   //     Trace("cdcac") << "Flip interval: " << flip_intervals[j] << std::endl;
    //   //     new_filp_intervals.emplace_back(CACInterval{d_nextIntervalId++, flip_intervals[j], {}, {}, {}, {}, {}});
    //   //   }
    //   //   return sampleOutsidewithDirection(new_filp_intervals, sample, _isOptimization == OPT_TYPE::MINIMIZATION);
    //   }
    // }
    return sampleOutsidewithDirection(infeasible, sample, _isOptimization == OPT_TYPE::MINIMIZATION);
  }
  if (options().arith.nlCovLinearModel != options::nlCovLinearModelMode::NONE
      && cur_variable < d_initialAssignment.size())
  {
    const poly::Value& suggested = d_initialAssignment[cur_variable];
    for (const auto& i : infeasible)
    {
      if (poly::contains(i.d_interval, suggested))
      {
        if (options().arith.nlCovLinearModel == options::nlCovLinearModelMode::INITIAL)
        {
          d_initialAssignment.clear();
        }
        return sampleOutside(infeasible, sample);
      }
    }
    Trace("cdcac") << "Using suggested initial value" << std::endl;
    sample = suggested;
    return true;
  }
  return sampleOutside(infeasible, sample);
}

namespace {

/**
 * This method follows the projection operator as detailed in algorithm 6 of
 * 10.1016/j.jlamp.2020.100633, which mostly follows the projection operator due
 * to McCallum. It uses all coefficients until one is either constant or does
 * not vanish over the current assignment.
 */
PolyVector requiredCoefficientsOriginal(const poly::Polynomial& p,
                                        const poly::Assignment& assignment)
{
  PolyVector res;
  for (long deg = degree(p); deg >= 0; --deg)
  {
    auto coeff = coefficient(p, deg);
    Assert(poly::is_constant(coeff)
           == lp_polynomial_is_constant(coeff.get_internal()));
    if (poly::is_constant(coeff)) break;
    res.add(coeff);
    if (evaluate_constraint(coeff, assignment, poly::SignCondition::NE))
    {
      break;
    }
  }
  return res;
}

/**
 * This method follows the original projection operator due to Lazard from
 * section 3 of 10.1007/978-1-4612-2628-4_29. It uses the leading and trailing
 * coefficient, and makes some limited efforts to avoid them in certain cases:
 * We avoid the leading coefficient if it is constant. We avoid the trailing
 * coefficient if the leading coefficient does not vanish over the current
 * assignment and the trailing coefficient is not constant.
 */
PolyVector requiredCoefficientsLazard(const poly::Polynomial& p,
                                      const poly::Assignment& assignment)
{
  PolyVector res;
  auto lc = poly::leading_coefficient(p);
  if (poly::is_constant(lc)) return res;
  res.add(lc);
  if (evaluate_constraint(lc, assignment, poly::SignCondition::NE)) return res;
  auto tc = poly::coefficient(p, 0);
  if (poly::is_constant(tc)) return res;
  res.add(tc);
  return res;
}

/**
 * This method follows the enhancements from 10.1007/978-3-030-60026-6_8 for the
 * projection operator due to Lazard, more specifically Section 3.3 and
 * Definition 4. In essence, we can skip the trailing coefficient if we can show
 * that p is not nullified by any n-1 dimensional point. The statement in the
 * paper is slightly more general, but there is no simple way to have such a
 * procedure T here. We simply try to show that T(f) = {} by using the extended
 * rewriter to simplify (and (= f_i 0)) (f_i being the coefficients of f) to
 * false.
 */
PolyVector requiredCoefficientsLazardModified(
    const poly::Polynomial& p,
    const poly::Assignment& assignment,
    VariableMapper& vm,
    Rewriter* rewriter)
{
  PolyVector res;
  auto lc = poly::leading_coefficient(p);
  // if leading coefficient is constant
  if (poly::is_constant(lc)) return res;
  // add leading coefficient
  res.add(lc);
  auto tc = poly::coefficient(p, 0);
  // if trailing coefficient is constant
  if (poly::is_constant(tc)) return res;
  // if leading coefficient does not vanish over the current assignment
  if (evaluate_constraint(lc, assignment, poly::SignCondition::NE)) return res;

  // construct phi := (and (= p_i 0)) with p_i the coefficients of p
  std::vector<Node> conditions;
  auto zero = NodeManager::currentNM()->mkConstReal(Rational(0));
  for (const auto& coeff : poly::coefficients(p))
  {
    conditions.emplace_back(NodeManager::currentNM()->mkNode(
        Kind::EQUAL, nl::as_cvc_polynomial(coeff, vm), zero));
  }
  // if phi is false (i.e. p can not vanish)
  Node rewritten =
      rewriter->extendedRewrite(NodeManager::currentNM()->mkAnd(conditions));
  if (rewritten.isConst())
  {
    Assert(rewritten.getKind() == Kind::CONST_BOOLEAN);
    Assert(!rewritten.getConst<bool>());
    return res;
  }
  // otherwise add trailing coefficient as well
  res.add(tc);
  return res;
}

}  // namespace

PolyVector CDCAC::requiredCoefficients(const poly::Polynomial& p)
{
  if (TraceIsOn("cdcac::projection"))
  {
    Trace("cdcac::projection")
        << "Poly: " << p << " over " << d_assignment << std::endl;
    Trace("cdcac::projection")
        << "Lazard:   " << requiredCoefficientsLazard(p, d_assignment)
        << std::endl;
    Trace("cdcac::projection")
        << "LMod: "
        << requiredCoefficientsLazardModified(
               p, d_assignment, d_constraints.varMapper(), d_env.getRewriter())
        << std::endl;
    Trace("cdcac::projection")
        << "Original: " << requiredCoefficientsOriginal(p, d_assignment)
        << std::endl;
  }
  switch (options().arith.nlCovProjection)
  {
    case options::nlCovProjectionMode::MCCALLUM:
      return requiredCoefficientsOriginal(p, d_assignment);
    case options::nlCovProjectionMode::LAZARD:
      return requiredCoefficientsLazard(p, d_assignment);
    case options::nlCovProjectionMode::LAZARDMOD:
      return requiredCoefficientsLazardModified(
          p, d_assignment, d_constraints.varMapper(), d_env.getRewriter());
    default:
      Assert(false);
      return requiredCoefficientsOriginal(p, d_assignment);
  }
}

PolyVector CDCAC::constructCharacterization(std::vector<CACInterval>& intervals)
{
  Assert(!intervals.empty()) << "A covering can not be empty";
  Trace("cdcac") << "Constructing characterization now" << std::endl;
  PolyVector res;

  for (std::size_t i = 0, n = intervals.size(); i < n - 1; ++i)
  {
    coverings::makeFinestSquareFreeBasis(intervals[i], intervals[i + 1]);
  }

  for (const auto& i : intervals)
  {
    Trace("cdcac") << "Considering " << i.d_interval << std::endl;
    Trace("cdcac") << "-> " << i.d_lowerPolys << " / " << i.d_upperPolys
                   << " and " << i.d_mainPolys << " / " << i.d_downPolys
                   << std::endl;
    Trace("cdcac") << "-> " << i.d_origins << std::endl;
    for (const auto& p : i.d_downPolys)
    {
      // Add all polynomial from lower levels.
      res.add(p);
    }
    for (const auto& p : i.d_mainPolys)
    {
      Trace("cdcac::projection")
          << "Discriminant of " << p << " -> " << discriminant(p) << std::endl;
      // Add all discriminants
      res.add(discriminant(p));

      // Add pairwise resultants
      for (const auto& q : i.d_mainPolys)
      {
        // avoid symmetric duplicates
        if (p >= q) continue;
        res.add(resultant(p, q));
      }

      for (const auto& q : requiredCoefficients(p))
      {
        // Add all required coefficients
        Trace("cdcac::projection")
            << "Coeff of " << p << " -> " << q << std::endl;
        res.add(q);
      }
      for (const auto& q : i.d_lowerPolys)
      {
        if (p == q) continue;
        // Check whether p(s \times a) = 0 for some a <= l
        if (!hasRootBelow(q, get_lower(i.d_interval))) continue;
        Trace("cdcac::projection") << "Resultant of " << p << " and " << q
                                   << " -> " << resultant(p, q) << std::endl;
        res.add(resultant(p, q));
      }
      for (const auto& q : i.d_upperPolys)
      {
        if (p == q) continue;
        // Check whether p(s \times a) = 0 for some a >= u
        if (!hasRootAbove(q, get_upper(i.d_interval))) continue;
        Trace("cdcac::projection") << "Resultant of " << p << " and " << q
                                   << " -> " << resultant(p, q) << std::endl;
        res.add(resultant(p, q));
      }
    }
  }

  for (std::size_t i = 0, n = intervals.size(); i < n - 1; ++i)
  {
    // Add resultants of consecutive intervals.
    for (const auto& p : intervals[i].d_upperPolys)
    {
      for (const auto& q : intervals[i + 1].d_lowerPolys)
      {
        Trace("cdcac::projection") << "Resultant of " << p << " and " << q
                                   << " -> " << resultant(p, q) << std::endl;
        res.add(resultant(p, q));
      }
    }
  }

  res.reduce();
  res.makeFinestSquareFreeBasis();

  return res;
}

CACInterval CDCAC::intervalFromCharacterization(
    const PolyVector& characterization,
    std::size_t cur_variable,
    const poly::Value& sample)
{
  PolyVector l;
  PolyVector u;
  PolyVector m;
  PolyVector d;

  for (const auto& p : characterization)
  {
    // Add polynomials to main
    m.add(p);
  }
  // Push lower-dimensional polys to down
  m.pushDownPolys(d, d_variableOrdering[cur_variable]);

  // Collect -oo, all roots, oo

  LazardEvaluation le(statisticsRegistry());
  prepareRootIsolation(le, cur_variable);
  std::vector<poly::Value> roots;
  roots.emplace_back(poly::Value::minus_infty());
  for (const auto& p : m)
  {
    Trace("cdcac") << "Isolating real roots of " << p << " over "
                   << d_assignment << std::endl;

    auto tmp = isolateRealRoots(le, p);
    roots.insert(roots.end(), tmp.begin(), tmp.end());
  }
  roots.emplace_back(poly::Value::plus_infty());
  std::sort(roots.begin(), roots.end());

  // Now find the interval bounds
  poly::Value lower;
  poly::Value upper;
  for (std::size_t i = 0, n = roots.size(); i < n; ++i)
  {
    if (sample < roots[i])
    {
      lower = roots[i - 1];
      upper = roots[i];
      break;
    }
    if (roots[i] == sample)
    {
      lower = sample;
      upper = sample;
      break;
    }
  }
  Assert(!is_none(lower) && !is_none(upper));

  if (!is_minus_infinity(lower))
  {
    // Identify polynomials that have a root at the lower bound
    d_assignment.set(d_variableOrdering[cur_variable], lower);
    for (const auto& p : m)
    {
      Trace("cdcac") << "Evaluating " << p << " = 0 over " << d_assignment
                     << std::endl;
      if (evaluate_constraint(p, d_assignment, poly::SignCondition::EQ))
      {
        l.add(p, true);
      }
    }
    d_assignment.unset(d_variableOrdering[cur_variable]);
  }
  if (!is_plus_infinity(upper))
  {
    // Identify polynomials that have a root at the upper bound
    d_assignment.set(d_variableOrdering[cur_variable], upper);
    for (const auto& p : m)
    {
      Trace("cdcac") << "Evaluating " << p << " = 0 over " << d_assignment
                     << std::endl;
      if (evaluate_constraint(p, d_assignment, poly::SignCondition::EQ))
      {
        u.add(p, true);
      }
    }
    d_assignment.unset(d_variableOrdering[cur_variable]);
  }

  if (lower == upper)
  {
    // construct a point interval
    return CACInterval{d_nextIntervalId++,
                       poly::Interval(lower, false, upper, false),
                       l,
                       u,
                       m,
                       d,
                       {}};
  }
  else
  {
    // construct an open interval
    Assert(lower < upper);
    return CACInterval{d_nextIntervalId++,
                       poly::Interval(lower, true, upper, true),
                       l,
                       u,
                       m,
                       d,
                       {}};
  }
}


CACInterval CDCAC::intervalFromSATCharacterization(
    const PolyVector& characterization,
    std::size_t cur_variable,
    const poly::Value& sample)
{
  PolyVector m;
  PolyVector d;

  for (const auto& p : characterization)
  {
    // Add polynomials to main
    m.add(p);
  }
  // Push lower-dimensional polys to down
  m.pushDownPolys(d, d_variableOrdering[cur_variable]);

  if(cur_variable == objectiveIndex){
    // 2023-12-04: optimization only compute once
    if(!objValue.has_computed_roots){
      LazardEvaluation le(statisticsRegistry());
      prepareRootIsolation(le, cur_variable);
      std::vector<poly::Value> roots;
      roots.emplace_back(poly::Value::minus_infty());
      for (const auto& p : m)
      {
        Trace("cdcac") << "Isolating real roots of " << p << " over "
                      << d_assignment << std::endl;

        auto tmp = isolateRealRoots(le, p);
        roots.insert(roots.end(), tmp.begin(), tmp.end());
      }
      roots.emplace_back(poly::Value::plus_infty());

      std::sort(roots.begin(), roots.end());
      objValue.roots.clear();
      objValue.roots.insert(objValue.roots.end(), roots.begin(), roots.end());
      
      // if(roots.size() == 0){
      //   objValue.roots_intervals.emplace_back(poly::Interval(poly::Value::minus_infty(), true, poly::Value::plus_infty(), true));
      // }
      // else{
      //   std::sort(roots.begin(), roots.end());
      //   objValue.roots.clear();
      //   objValue.roots.insert(objValue.roots.end(), roots.begin(), roots.end());
      //   // construct root intervals in order to find the interval bounds
      //   for(size_t i=0;i<roots.size();i++){
      //     if(i == 0){
      //       objValue.roots_intervals.emplace_back(poly::Interval(poly::Value::minus_infty(), true, roots[i], true));
      //       objValue.roots_intervals.emplace_back(poly::Interval(roots[i], false, roots[i], false));
      //     }
      //     else if (i == roots.size()-1){
      //       objValue.roots_intervals.emplace_back(poly::Interval(roots[i], false, roots[i], false));
      //       objValue.roots_intervals.emplace_back(poly::Interval(roots[i], true, poly::Value::plus_infty(), true));
      //     }
      //     else{
      //       objValue.roots_intervals.emplace_back(poly::Interval(roots[i], false, roots[i], false));
      //       objValue.roots_intervals.emplace_back(poly::Interval(roots[i], true, roots[i+1], true));
      //     }
      //   }
      // }
      objValue.has_computed_roots = true;
    }
    
    // objValue.roots.emplace_back(poly::Value::minus_infty());
    // objValue.roots.emplace_back(poly::Value::plus_infty());
    // std::sort(objValue.roots.begin(), objValue.roots.end());
    // Now find the interval bounds
    poly::Value lower;
    poly::Value upper;
    for (std::size_t i = 0, n = objValue.roots.size(); i < n; ++i)
    {
      if (sample < objValue.roots[i])
      {
        lower = objValue.roots[i - 1];
        upper = objValue.roots[i];
        break;
      }
      if (objValue.roots[i] == sample)
      {
        lower = sample;
        upper = sample;
        break;
      }
    }

    Assert(!is_none(lower) && !is_none(upper));

    if (lower == upper)
    {
      // construct a point interval
      return CACInterval{d_nextIntervalId++,
                        poly::Interval(lower, false, upper, false),
                        {},
                        {},
                        m,
                        d,
                        {}};
    }
    else
    {
      // construct an open interval
      Assert(lower < upper);
      return CACInterval{d_nextIntervalId++,
                        poly::Interval(lower, true, upper, true),
                        {},
                        {},
                        m,
                        d,
                        {}};
    }
  }
  else{
    poly::Value lower = poly::Value::minus_infty();
    poly::Value upper = poly::Value::plus_infty();
    return CACInterval{d_nextIntervalId++,
                        poly::Interval(lower, false, upper, false),
                        {},
                        {},
                        m,
                        d,
                        {}};
  }
}

std::vector<CACInterval> CDCAC::getUnsatCoverImpl(std::size_t curVariable,
                                                  bool returnFirstInterval)
{
  // anynomous author: Implementation of main algorithm
  d_env.getResourceManager()->spendResource(Resource::ArithNlCoveringStep);
  Trace("cdcac") << "Looking for unsat cover for "
                 << d_variableOrdering[curVariable] << std::endl;
  // anynomous author: II = get_unsat_intervals(s) -> algorithm 3.
  std::vector<CACInterval> intervals = getUnsatIntervals(curVariable);

  if (TraceIsOn("cdcac"))
  {
    Trace("cdcac") << "Unsat intervals for " << d_variableOrdering[curVariable]
                   << ":" << std::endl;
    for (const auto& i : intervals)
    {
      Trace("cdcac") << "-> " << i.d_interval << " from " << i.d_origins
                     << std::endl;
    }
  }
  poly::Value sample;

  // anynomous author: s_i = sample_outside(II)
  while (sampleOutsideWithInitial(intervals, sample, curVariable))
  { 
    // anynomous author: integer variable, it is not needed in non-linear real arithmetic optimization.
    if (!checkIntegrality(curVariable, sample))
    {
      // the variable is integral, but the sample is not.
      Trace("cdcac") << "Used " << sample << " for integer variable "
                     << d_variableOrdering[curVariable] << std::endl;
      auto newInterval = buildIntegralityInterval(curVariable, sample);
      Trace("cdcac") << "Adding integrality interval " << newInterval.d_interval
                     << std::endl;
      intervals.emplace_back(newInterval);
      pruneRedundantIntervals(intervals);
      continue;
    }

    // anynomous author: i == n here !!! ... 
    d_assignment.set(d_variableOrdering[curVariable], sample);

    // std::cout<<"++++++++++++++++++++"<<std::endl;
    // std::cout<<"Current Variable: "<<d_variableOrdering[curVariable]<<std::endl;
    std::vector<poly::Interval> feasibles;
    std::vector<poly::Interval> infs;
    for(size_t i=0;i<intervals.size();i++){
      infs.emplace_back(intervals[i].d_interval);
    //   std::cout<<"infeasibles: "<<infs[i]<<std::endl;
    }
    feasibles = intervalMinus(poly::Interval().full(), infs);
    // for(size_t i=0;i<feasibles.size();i++){
    //   std::cout<<"feasibles: "<<feasibles[i]<<std::endl;
    // }
    // std::cout<<"++++++++++++++++++++"<<std::endl;

    if(isOptimization() && curVariable == objectiveIndex){
      // anynomous author: check whether there is only one left interval
      //      return false, false, ..., true, true. (Finally if only one interval, it will return true forever).
      // objValue.maybeUnbounded = checkUnbounded(intervals, objValue.unboundedProof);
      std::vector<poly::Interval> infeasibles;
      for(size_t i=0;i<intervals.size();i++){
        infeasibles.emplace_back(intervals[i].d_interval);
        // std::cout<<"infeasibles: "<<infeasibles[i]<<std::endl;
      }
      objValue.feasibles = intervalMinus(poly::Interval().full(), infeasibles);
      // for(size_t i=0;i<objValue.feasibles.size();i++){
      //   std::cout<<"feasibles: "<<objValue.feasibles[i]<<std::endl;
      // }
      // anynomous author: it only used for unsat branch lemma
      objValue.objCurVal = objValue.obj_value_to_node(sample, objValue.objective);
    }
    Trace("cdcac") << "Sample: " << d_assignment << std::endl;
    // anynomous author: if i == n then return (SAT, (s_1, ..., s_{i-1}, s_i))
    if (curVariable == d_variableOrdering.size() - 1)
    {
      if(isOptimization()){
        if(!objValue.isSAT()) objValue.setSAT();
        objValue.setCurSAT();
        setCurAssignment(); // set current assignment
        objValue.setCurModelValue(d_assignment.get(d_variableOrdering[objectiveIndex]));
        // std::cout<<"current assignment: "<<objValue.curAssignment<<std::endl;

        // current track is sat
        Trace("cdcac") << "Found full assignment: " << d_assignment << std::endl;
        sampleSAT = true;
        objValue.set_removing_sat_assignment();
        return getSatIntervals(curVariable);
      }
      else{
        // We have a full assignment. SAT!
        Trace("cdcac") << "Found full assignment: " << d_assignment << std::endl;
        return {};
      }
    }

    if (isProofEnabled())
    {
      d_proof->startScope();
      d_proof->startRecursive();
    }
    // Recurse to next variable
    // anynomous author: (f, O) = get_unsat_cover((s_1, ..., s_{i-1}, s_i))
    auto cov = getUnsatCoverImpl(curVariable + 1);
    if(isOptimization() && objValue.isCurSAT()){
      // anynomous author: is optimization && found a model
      //      so we need to rule out the satisfiable space.
      //      cov is a full set of polynomials.

      if(objValue._removing_sat_assignment){
        // TODO current improvment

        Trace("cdcac") << "Optimization Refuting Sample: " << d_assignment << std::endl;
        // anynomous author: else if f == UNSAT then 
        // anynomous author: R = construct_characterization((s_1, ..., s_{i-1}, s_i), O) -> algorithm 4
        auto characterization = constructCharacterization(cov);
        Trace("cdcac") << "Optimization Characterization: " << characterization << std::endl;
        d_assignment.unset(d_variableOrdering[curVariable]);

        Trace("cdcac") << "Optimization Building interval..." << std::endl;
        // anynomous author: I = interval_from_characterization((s_1, ..., s_{i-1}), s_i, R) -> algorithm 5
        
        auto newInterval =
            intervalFromSATCharacterization(characterization, curVariable, sample);
        Trace("cdcac") << "Optimization new interval: " << newInterval.d_interval << std::endl;
        objValue.analyze_cell(newInterval, intervals);
        newInterval.d_origins = collectConstraints(cov);
        // // anynomous author: 2023-11-02, e.g. coefficient (/ (- 262984456819) 4860000000000000000000000000000000000000)
        // AlwaysAssert(check_normal_polynomials(newInterval.d_origins));
        // anynomous author: II = I \union {I}
        intervals.emplace_back(newInterval);

        if (returnFirstInterval)
        {
          return intervals;
        }

        Trace("cdcac") << "Optimization Added " << intervals.back().d_interval << std::endl;
        Trace("cdcac") << "\tOptimization lower:   " << intervals.back().d_lowerPolys
                      << std::endl;
        Trace("cdcac") << "\tOptimization upper:   " << intervals.back().d_upperPolys
                      << std::endl;
        Trace("cdcac") << "\tOptimization main:    " << intervals.back().d_mainPolys
                      << std::endl;
        Trace("cdcac") << "\tOptimization down:    " << intervals.back().d_downPolys
                      << std::endl;
        Trace("cdcac") << "\tOptimization origins: " << intervals.back().d_origins << std::endl;

        // Remove redundant intervals
        pruneRedundantIntervals(intervals);

        if(curVariable == objectiveIndex && sampleSAT){
          // anynomous author: recursive to the objective variable
          //      so we can obtain the model value, bound value, and optimized value.
          //      for example, maximize obj, feasible interval is (1, 3), and assign obj 2;
          //      model value: 2; bound value: 3; optimized value: 3 - \epsilon.

          // for(size_t i=0;i<intervals.size();i++){
          //   std::cout<<intervals[i].d_interval<<std::endl;
          // }

          // anynomous author: 2023-08-25: distinct intervals:
          //      (-oo, +oo) from Characterization
          //      current model value is the final optimal
          intervals.emplace_back(optimizedInterval(objValue.curModelValue));
          // std::cout<<objValue.curModelValue<<std::endl;
          // for(size_t i=0;i<intervals.size();i++){
          //   std::cout<<intervals[i].d_interval<<std::endl;
          // }
          pruneRedundantIntervals(intervals);
          objValue.setInfeasibleIntervals(intervals);
        }
      }
      else{
        Trace("cdcac") << "Optimization Refuting Sample: " << d_assignment << std::endl;
        // anynomous author: else if f == UNSAT then 
        // anynomous author: R = construct_characterization((s_1, ..., s_{i-1}, s_i), O) -> algorithm 4
        auto characterization = constructCharacterization(cov);
        Trace("cdcac") << "Optimization Characterization: " << characterization << std::endl;
        d_assignment.unset(d_variableOrdering[curVariable]);

        Trace("cdcac") << "Optimization Building interval..." << std::endl;
        // anynomous author: I = interval_from_characterization((s_1, ..., s_{i-1}), s_i, R) -> algorithm 5
        auto newInterval =
            intervalFromCharacterization(characterization, curVariable, sample);
        Trace("cdcac") << "Optimization new interval: " << newInterval.d_interval << std::endl;
        if(curVariable == objectiveIndex){
          // 2023-09-08: analyze the cell
          objValue.analyze_cell(newInterval, intervals);
        }
        newInterval.d_origins = collectConstraints(cov);
        // // anynomous author: 2023-11-02, e.g. coefficient (/ (- 262984456819) 4860000000000000000000000000000000000000)
        // AlwaysAssert(check_normal_polynomials(newInterval.d_origins));
        // anynomous author: II = I \union {I}
        intervals.emplace_back(newInterval);

        if (returnFirstInterval)
        {
          return intervals;
        }

        Trace("cdcac") << "Optimization Added " << intervals.back().d_interval << std::endl;
        Trace("cdcac") << "\tOptimization lower:   " << intervals.back().d_lowerPolys
                      << std::endl;
        Trace("cdcac") << "\tOptimization upper:   " << intervals.back().d_upperPolys
                      << std::endl;
        Trace("cdcac") << "\tOptimization main:    " << intervals.back().d_mainPolys
                      << std::endl;
        Trace("cdcac") << "\tOptimization down:    " << intervals.back().d_downPolys
                      << std::endl;
        Trace("cdcac") << "\tOptimization origins: " << intervals.back().d_origins << std::endl;

        // Remove redundant intervals
        pruneRedundantIntervals(intervals);

        if(curVariable == objectiveIndex && sampleSAT){
          // anynomous author: recursive to the objective variable
          //      so we can obtain the model value, bound value, and optimized value.
          //      for example, maximize obj, feasible interval is (1, 3), and assign obj 2;
          //      model value: 2; bound value: 3; optimized value: 3 - \epsilon.

          // for(size_t i=0;i<intervals.size();i++){
          //   std::cout<<intervals[i].d_interval<<std::endl;
          // }

          // anynomous author: 2023-08-25: distinct intervals:
          //      (-oo, +oo) from Characterization
          //      current model value is the final optimal
          intervals.emplace_back(optimizedInterval(objValue.curModelValue));
          // std::cout<<objValue.curModelValue<<std::endl;
          // for(size_t i=0;i<intervals.size();i++){
          //   std::cout<<intervals[i].d_interval<<std::endl;
          // }
          pruneRedundantIntervals(intervals);
          objValue.setInfeasibleIntervals(intervals);
        }
      }
      // end of optimization 
    }
    else{
      if (cov.empty())
      {
        // Found SAT!
        Trace("cdcac") << "SAT!" << std::endl;
        return {};
      }
      Trace("cdcac") << "Refuting Sample: " << d_assignment << std::endl;
      // anynomous author: else if f == UNSAT then 
      // anynomous author: R = construct_characterization((s_1, ..., s_{i-1}, s_i), O) -> algorithm 4
      auto characterization = constructCharacterization(cov);
      Trace("cdcac") << "Characterization: " << characterization << std::endl;

      d_assignment.unset(d_variableOrdering[curVariable]);

      Trace("cdcac") << "Building interval..." << std::endl;
      // anynomous author: I = interval_from_characterization((s_1, ..., s_{i-1}), s_i, R) -> algorithm 5
      auto newInterval =
          intervalFromCharacterization(characterization, curVariable, sample);
      Trace("cdcac") << "New interval: " << newInterval.d_interval << std::endl;
      newInterval.d_origins = collectConstraints(cov);
      // anynomous author: II = I \union {I}
      intervals.emplace_back(newInterval);
      if (isProofEnabled())
      {
        d_proof->endRecursive(newInterval.d_id);
        auto cell = d_proof->constructCell(
            d_constraints.varMapper()(d_variableOrdering[curVariable]),
            newInterval,
            d_assignment,
            sample,
            d_constraints.varMapper());
        d_proof->endScope(cell);
      }

      if (returnFirstInterval)
      {
        return intervals;
      }

      Trace("cdcac") << "Added " << intervals.back().d_interval << std::endl;
      Trace("cdcac") << "\tlower:   " << intervals.back().d_lowerPolys
                    << std::endl;
      Trace("cdcac") << "\tupper:   " << intervals.back().d_upperPolys
                    << std::endl;
      Trace("cdcac") << "\tmain:    " << intervals.back().d_mainPolys
                    << std::endl;
      Trace("cdcac") << "\tdown:    " << intervals.back().d_downPolys
                    << std::endl;
      Trace("cdcac") << "\torigins: " << intervals.back().d_origins << std::endl;

      // Remove redundant intervals
      pruneRedundantIntervals(intervals);
    }

    // anynomous author: now to sample a new opt value, reinit the flag
    if(objValue.is_removing_sat_assignment() && isOptimization() && curVariable == objectiveIndex){
      sampleSAT = false; 
      objValue.unset_removing_sat_assignment();
    }
  }

  if (TraceIsOn("cdcac"))
  {
    Trace("cdcac") << "Returning intervals for "
                   << d_variableOrdering[curVariable] << ":" << std::endl;
    for (const auto& i : intervals)
    {
      Trace("cdcac") << "-> " << i.d_interval << std::endl;
    }
  }
  return intervals;
}

std::vector<CACInterval> CDCAC::getUnsatCover(bool returnFirstInterval)
{
  if (isProofEnabled())
  {
    d_proof->startRecursive();
  }
  objValue.unsetCurSAT();
  auto res = getUnsatCoverImpl(0, returnFirstInterval);
  if(objValue.isCurSAT()){
    setOptValues();
  }
  objValue.has_computed_roots = false;
  objValue.roots.clear();
  // for(size_t i=0;i<res.size();i++){
  //   std::cout<<i<<" "<<res[i].d_interval<<std::endl;
  // }
  if (isProofEnabled())
  {
    d_proof->endRecursive(0);
  }
  return res;
}

void CDCAC::startNewProof()
{
  if (isProofEnabled())
  {
    d_proof->startNewProof();
  }
}

ProofGenerator* CDCAC::closeProof(const std::vector<Node>& assertions)
{
  if (isProofEnabled())
  {
    d_proof->endScope(assertions);
    return d_proof->getProofGenerator();
  }
  return nullptr;
}

bool CDCAC::checkIntegrality(std::size_t cur_variable, const poly::Value& value)
{
  Node var = d_constraints.varMapper()(d_variableOrdering[cur_variable]);
  if (var.getType() != NodeManager::currentNM()->integerType())
  {
    // variable is not integral
    return true;
  }
  return poly::represents_integer(value);
}

CACInterval CDCAC::buildIntegralityInterval(std::size_t cur_variable,
                                            const poly::Value& value)
{
  poly::Variable var = d_variableOrdering[cur_variable];
  poly::Integer below = poly::floor(value);
  poly::Integer above = poly::ceil(value);
  // construct var \in (below, above)
  return CACInterval{d_nextIntervalId++,
                     poly::Interval(below, above),
                     {var - below},
                     {var - above},
                     {var - below, var - above},
                     {},
                     {}};
}

bool CDCAC::hasRootAbove(const poly::Polynomial& p,
                         const poly::Value& val) const
{
  auto roots = poly::isolate_real_roots(p, d_assignment);
  return std::any_of(roots.begin(), roots.end(), [&val](const poly::Value& r) {
    return r >= val;
  });
}

bool CDCAC::hasRootBelow(const poly::Polynomial& p,
                         const poly::Value& val) const
{
  auto roots = poly::isolate_real_roots(p, d_assignment);
  return std::any_of(roots.begin(), roots.end(), [&val](const poly::Value& r) {
    return r <= val;
  });
}

void CDCAC::pruneRedundantIntervals(std::vector<CACInterval>& intervals)
{
  cleanIntervals(intervals);
  if (options().arith.nlCovPrune)
  {
    if (TraceIsOn("cdcac"))
    {
      auto copy = intervals;
      removeRedundantIntervals(intervals);
      if (copy.size() != intervals.size())
      {
        Trace("cdcac") << "Before pruning:";
        for (const auto& i : copy) Trace("cdcac") << " " << i.d_interval;
        Trace("cdcac") << std::endl;
        Trace("cdcac") << "After pruning: ";
        for (const auto& i : intervals) Trace("cdcac") << " " << i.d_interval;
        Trace("cdcac") << std::endl;
      }
    }
    else
    {
      removeRedundantIntervals(intervals);
    }
  }
  if (isProofEnabled())
  {
    d_proof->pruneChildren([&intervals](std::size_t id) {
      if (id == 0) return false;
      return std::find_if(intervals.begin(),
                          intervals.end(),
                          [id](const CACInterval& i) { return i.d_id == id; })
             == intervals.end();
    });
  }
}

void CDCAC::prepareRootIsolation(LazardEvaluation& le,
                                 size_t cur_variable) const
{
  if (options().arith.nlCovLifting == options::nlCovLiftingMode::LAZARD)
  {
    for (size_t vid = 0; vid < cur_variable; ++vid)
    {
      const auto& val = d_assignment.get(d_variableOrdering[vid]);
      le.add(d_variableOrdering[vid], val);
    }
    le.addFreeVariable(d_variableOrdering[cur_variable]);
  }
}

std::vector<poly::Value> CDCAC::isolateRealRoots(
    LazardEvaluation& le, const poly::Polynomial& p) const
{
  if (options().arith.nlCovLifting == options::nlCovLiftingMode::LAZARD)
  {
    return le.isolateRealRoots(p);
  }
  return poly::isolate_real_roots(p, d_assignment);
}

// anynomous author: optimization
bool CDCAC::isOptimization() const{
  return _isOptimization != OPT_TYPE::NON_OPT;
}
void CDCAC::setOptimization(){
  _isOptimization = OPT_TYPE::WAITING;
  // std::cout<<"CDCAC::setOptimization"<<std::endl;
}
void CDCAC::setObjective(OPT_TYPE _isOpt, Node& e){
  // std::cout<<"CDCAC::setObjective"<<std::endl;
  _isOptimization = _isOpt;
  objectiveVariable = e;
  d_varOrder.setObjectiveVariable(e);
  objValue.setObjective(_isOpt, e);
}

void CDCAC::assertOptBound(){
  objValue.assertOptBound();
}
bool CDCAC::missBound() const{
  return objValue.missBound();
}
Node CDCAC::getBoundValue(const Node& e) const{
  Assert(objValue.objective == e);
  return objValue.getBoundValue();
}
Node CDCAC::getOptimizedValue(const Node& e) const{
  Assert(objValue.objective == e);
  return objValue.getOptimizedValue();
}
std::vector<CACInterval> CDCAC::getSatIntervals(std::size_t cur_variable){
  // 2023-11-06: use lazard to analyze the infeasible regions.
  
  // std::vector<CACInterval> res;
  // LazardEvaluation le(statisticsRegistry());
  // prepareRootIsolation(le, cur_variable);
  // std::vector<poly::Interval> intervals;
  // for (const auto& c : d_constraints.getConstraints())
  // {
  //   const poly::Polynomial& p = std::get<0>(c);
  //   poly::SignCondition sc = std::get<1>(c);
  //   const Node& n = std::get<2>(c);

  //   // if (main_variable(p) != d_variableOrdering[cur_variable])
  //   // {
  //   //   // Constraint is in another variable, ignore it.
  //   //   continue;
  //   // }

  //   Trace("cdcac") << "Infeasible intervals for " << p << " " << sc
  //                  << " 0 over " << d_assignment << std::endl;
  //   std::vector<poly::Interval> intervals;
  //   if (options().arith.nlCovLifting
  //       == options::nlCovLiftingMode::LAZARD)
  //   {
  //     intervals = le.infeasibleRegions(p, ConditionNot(sc));
  //     if (TraceIsOn("cdcac"))
  //     {
  //       auto reference = poly::infeasible_regions(p, d_assignment, ConditionNot(sc));
  //       Trace("cdcac") << "Lazard: " << intervals << std::endl;
  //       Trace("cdcac") << "Regular: " << reference << std::endl;
  //     }
  //   }
  //   else
  //   {
  //     intervals = poly::infeasible_regions(p, d_assignment, ConditionNot(sc));
  //   }
  //   for (const auto& i : intervals)
  //   {
  //     Trace("cdcac") << "-> " << i << std::endl;
  //     PolyVector l, u, m, d;
  //     m.add(p);
  //     m.pushDownPolys(d, d_variableOrdering[cur_variable]);
  //     if (!is_minus_infinity(get_lower(i))) l = m;
  //     if (!is_plus_infinity(get_upper(i))) u = m;
  //     res.emplace_back(CACInterval{d_nextIntervalId++, i, l, u, m, d, {n}});
  //   }
  // }
  // pruneRedundantIntervals(res);
  // return res;

  // collect all satisfiable polynomials
  std::vector<CACInterval> res;
  std::vector<Node> origin;
  PolyVector m, d;
  poly::Value lower = poly::Value::minus_infty();
  poly::Value upper = poly::Value::plus_infty();
  for (const auto& c : d_constraints.getConstraints())
  {
    const poly::Polynomial& p = std::get<0>(c);
    // poly::SignCondition sc = std::get<1>(c);
    const Node& n = std::get<2>(c);
  
    // TODO
    // if (main_variable(p) != d_variableOrdering[cur_variable])
    // {
    //   // Constraint is in another variable, ignore it.
    //   continue;
    // }

    m.add(p);
    m.pushDownPolys(d, d_variableOrdering[cur_variable]);
    origin.emplace_back(n);
  }
  res.emplace_back(CACInterval{d_nextIntervalId++,
                       poly::Interval(lower, false, upper, false), // TODO, 2023-11-06: maybe error!
                       {},
                       {},
                       m,
                       d,
                       origin});
  // pruneRedundantIntervals(res); // anynomous author: no need to prune
  // std::cout<<res[0].d_interval<<std::endl;
  return res;
}
void CDCAC::setCurAssignment(){
  objValue.curAssignment.clear();
  for (const auto& var : d_variableOrdering)
  {
    objValue.setCurAssignment(var, d_assignment.get(var));
  }
}
bool CDCAC::isOptSAT() const{
  return objValue.isSAT();
}

bool CDCAC::isCurSAT() const{
  return objValue.isCurSAT();
}

CACInterval CDCAC::optimizedInterval(const poly::Value& sample){
  // auto* nm = NodeManager::currentNM();
  if(_isOptimization == OPT_TYPE::MAXIMIZATION){
    return CACInterval{d_nextIntervalId++,
                       poly::Interval(poly::Value::minus_infty(), true, sample, false),
                       {},
                       {},
                       {},
                       {},
                       {}};
                      //  {nm->mkNode(GT, objectiveVariable, value_to_node(sample, objectiveVariable))}};
  }
  else{
    // minimization
    return CACInterval{d_nextIntervalId++,
                       poly::Interval(sample, false, poly::Value::plus_infty(), true),
                       {},
                       {},
                       {},
                       {},
                       {}};
                      //  {nm->mkNode(LT, objectiveVariable, value_to_node(sample, objectiveVariable))}};
  }
}
void CDCAC::setOptValues(){
  if(objValue.first){ objValue.first = false; }
  objValue.optModelValue = objValue.curModelValue;
  objValue.optBoundValue = objValue.curBoundValue;
  objValue.optOptimizedValue = objValue.curOptimizedValue;
  // note that current opt must more optimized than previous opt
  objValue.optAssignment.clear();
  for (const auto& var : d_variableOrdering)
  {
    objValue.setOptAssignment(var, objValue.curAssignment.get(var));
  }
  // don't forget to add increment lemma to solvers
}
void CDCAC::getOptModelCache(std::map<Node, Node>& optCache){
  for(size_t i=0;i<d_variableOrdering.size();i++){
    Node var = d_constraints.varMapper()(d_variableOrdering[i]);
    Node opt_value = objValue.getOptimizedAssignment(d_variableOrdering[i], var);
    optCache.insert(std::pair<Node, Node>(var, opt_value));
  }
}
bool CDCAC::isOptUnbounded() const{
  return objValue.isUnbounded();
}
bool CDCAC::isOptPosInf() const{
  return objValue.isPosInf();
}
bool CDCAC::isOptNegInf() const{
  return objValue.isNegInf();
}
bool CDCAC::isOptPosApprox() const{
  return objValue.isPosApprox();
}
bool CDCAC::isOptNegApprox() const{
  return objValue.isNegApprox();
}

void CDCAC::get_coefficients(const Node& p, std::vector<poly::Value>& coes){
  if(p.isConst()){
    coes.emplace_back(poly_utils::toRational(p.getConst<Rational>()));
  }
  else{
    for(auto i=p.begin();i!=p.end();i++){
      if((*i).isConst()){
        coes.emplace_back(poly_utils::toRational((*i).getConst<Rational>()));
      }
      else{
        get_coefficients(*i, coes);
      }
    }
  }
}
bool CDCAC::check_normal_polynomials(const std::vector<Node>& origins){
  poly::Value pos_epsilon(poly::Rational(1, 1000000000000)); // 1e-12
  poly::Value neg_epsilon(poly::Rational(-1, 1000000000000)); // -1e-12
  for(size_t i=0;i<origins.size();i++){
    std::vector<poly::Value> coes;
    get_coefficients(origins[i], coes);
    for(size_t j=0;j<coes.size();j++){
      if((coes[j] > 0 && coes[j] < pos_epsilon) || (coes[j] < 0 && coes[j] > neg_epsilon)){
        // std::cout<<coes[j]<<std::endl;
        return false;
      }
    }
  }
  return true;
}


void objectiveValue::setObjective(OPT_TYPE _isOpt, Node& e){
  // std::cout<<"objectiveValue::setObjective"<<std::endl;
  _isOptimization = _isOpt;
  objective = e;
}
// current
void objectiveValue::setCurModelValue(const poly::Value& val){
  curModelValue = val;
}
void objectiveValue::setInfeasibleIntervals(const std::vector<CACInterval>& infs){
  infeasibleIntervals.clear();
  infeasibleIntervals.assign(infs.begin(), infs.end());
  analyzeInfeasibleIntervals();
}
void objectiveValue::analyzeInfeasibleIntervals(){
  if(_isOptimization == OPT_TYPE::MAXIMIZATION){
    curOptimizedValue = OPT_VALUE_TYPE::MINUS_EPSILON;
  }
  else if(_isOptimization == OPT_TYPE::MINIMIZATION){
    curOptimizedValue = OPT_VALUE_TYPE::PLUS_EPSILON;
  }

  // bool found = false;
  for(size_t i=0;i<infeasibleIntervals.size();i++){
    const auto& itv = infeasibleIntervals[i].d_interval;
    
    if(poly::is_point(itv)){
      // itv is an point interval
      const lp_value_t* l = &(itv.get_internal()->a);
      int pc = lp_value_cmp(curModelValue.get_internal(), l);
      if(pc == 2){
        // found = true;
        // curModelValue == itv.b == itv.a
        curOptimizedValue = OPT_VALUE_TYPE::EXACT;
        curBoundValue = poly::Value(l);
        return;
      }
    }
    else{
      const lp_value_t* l = &(itv.get_internal()->a);
      const lp_value_t* u = &(itv.get_internal()->b);

      int lc = lp_value_cmp(curModelValue.get_internal(), l);
      int uc = lp_value_cmp(curModelValue.get_internal(), u);
      if(lc > 0 && uc < 0){
        // l < curModelValue < u
        // found = true;
        if(_isOptimization == OPT_TYPE::MAXIMIZATION){
          curBoundValue = poly::Value(u);
        }
        else if(_isOptimization == OPT_TYPE::MINIMIZATION){
          curBoundValue = poly::Value(l);
        }
        return;
      }
    }
  }
  Assert(false);
}
void objectiveValue::setCurAssignment(const poly::Variable &var, const poly::Value& val){
  curAssignment.set(var, val);
}

void objectiveValue::setOptAssignment(const poly::Variable &var, const poly::Value& val){
  optAssignment.set(var, val);
}
// optimized
void objectiveValue::setSAT(){
  _isSAT = true;
}
void objectiveValue::setCurSAT(){
  _isCurSAT = true;
}
void objectiveValue::unsetCurSAT(){
  _isCurSAT = false;
  // clear
  curAssignment.clear();
}
bool objectiveValue::isSAT() const{
  return _isSAT;
}
bool objectiveValue::isCurSAT() const{
  return _isCurSAT;
}
void objectiveValue::assertOptBound(){
  curOptimizedValue = OPT_VALUE_TYPE::EXACT;
}

Node objectiveValue::obj_value_to_node(const poly::Value &v, const Node& var) const{
  Assert(!is_minus_infinity(v)) << "Can not convert minus infinity.";
  Assert(!is_none(v)) << "Can not convert none.";
  Assert(!is_plus_infinity(v)) << "Can not convert plus infinity.";

  auto* nm = NodeManager::currentNM();
  if(var.getType().isReal()){
    // std::cout<<"isReal"<<std::endl;
    if (is_algebraic_number(v))
    {
      auto ran = as_algebraic_number(v);
      return nm->mkRealAlgebraicNumber(RealAlgebraicNumber(std::move(ran)));
    }
    if (is_dyadic_rational(v))
    {
      return nm->mkConstReal(poly_utils::toRational(as_dyadic_rational(v)));
    }
    if (is_integer(v))
    {
      return nm->mkConstReal(poly_utils::toRational(as_integer(v)));
    }
    if (is_rational(v))
    {
      return nm->mkConstReal(poly_utils::toRational(as_rational(v)));
    }
  }
  else if(var.getType().isInteger()){
    return nm->mkConstInt(poly_utils::toRational(as_integer(v)));
    // anynomous author: 2023-05-30: maybe it will lead to an error.
  }
  Assert(false) << "All cases should be covered.";
  return nm->mkConstReal(Rational(0));
}
Node objectiveValue::getBoundValue() const{
  return obj_value_to_node(optAssignment.get(objVar), objective);
}
Node objectiveValue::getOptimizedAssignment(const poly::Variable& pvar, const Node& var) const{
  // return obj_value_to_node(optAssignment.get(pvar), var);
  if(objective == var && (isApprox())) return obj_value_to_node(optApproxValue, objective);
  else return obj_value_to_node(optAssignment.get(pvar), var);
}
Node objectiveValue::getOptimizedValue() const{
  if(isApprox()) return obj_value_to_node(optApproxValue, objective);
  else return obj_value_to_node(optAssignment.get(objVar), objective);
}
bool objectiveValue::missBound() const{
  return optOptimizedValue != OPT_VALUE_TYPE::EXACT;
}
const poly::Assignment& objectiveValue::getModel() const{
  // std::cout<<"output get-model: "<<optAssignment<<std::endl;
  return optAssignment;
}

void objectiveValue::setPosUnbounded(){
  _isUnbounded = true;
  _isPosInf = true;
  _isApprox = false;
}
void objectiveValue::setNegUnbounded(){
  _isUnbounded = true;
  _isPosInf = false;
  _isApprox = false;
}
void objectiveValue::setPosApprox(){
  _isUnbounded = true;
  _isPosApprox = true;
  _isApprox = true;
}
void objectiveValue::setNegApprox(){
  _isUnbounded = true;
  _isPosApprox = false;
  _isApprox = true;
}
bool objectiveValue::isUnbounded() const{
  return _isUnbounded;
}
bool objectiveValue::isApprox() const{
  return _isApprox;
}
bool objectiveValue::isPosInf() const{
  return _isUnbounded && _isPosInf && !_isApprox;
}
bool objectiveValue::isNegInf() const{
  return _isUnbounded && !_isPosInf && !_isApprox;
}
bool objectiveValue::isPosApprox() const{
  return _isUnbounded && _isPosApprox && _isApprox;
}
bool objectiveValue::isNegApprox() const{
  return _isUnbounded && !_isPosApprox && _isApprox;
}

bool objectiveValue::isMax() const{
  return _isOptimization == OPT_TYPE::MAXIMIZATION;
}
bool objectiveValue::isMin() const{
  return _isOptimization == OPT_TYPE::MINIMIZATION;
}

Node objectiveValue::mkUnsatOptLemma(){
  auto* nm = NodeManager::currentNM();
  Assert(!isCurSAT());
  return nm->mkNode(EQUAL, objective, objCurVal).notNode();
}
Node objectiveValue::mkIncrementLemma(){
  auto* nm = NodeManager::currentNM();
  if(isPosInf() || isNegInf()) return nm->mkConst(false); // already Inf
  else{
    auto val = optAssignment.get(objVar);
    if(isApprox()) val = optApproxValue;

    // // anynomous author: TODO, 2024-01-12, it is incomplete but help fix a bug of real algebraic number lemma
    // // Because when go to another branch the lower/upper bound may cover a root.

    // anynomous author: From src/expr/node_manager_template.h, we know that real algebraic number
    // in order to keep completeness, we have to make a new lemma
    // Because 7 false instances cannot be resolved

    // if(poly::is_algebraic_number(val)){
    //   // if(isMax()){
    //   //   if(isNegApprox())
    //   //     val =  
    //   //   else
    //   //     val = 
    //   // }
    //   // else{
    //   //   if(isPosApprox())
    //   //     val = 
    //   //   else
    //   //     val = 
    //   // }
    //   val = isMin()?poly::get_lower_bound(poly::as_algebraic_number(val)):poly::get_upper_bound(poly::as_algebraic_number(val));
    // }
    if(poly::is_algebraic_number(val)){
      // // add a polynomial representation via constraints
      Node x_ran = nm->mkBoundVar(objective.getType());
      // auto dp = poly::get_defining_polynomial(poly::as_algebraic_number(val));
      // auto lower_c = nm->mkNode(GT, x_ran, value_to_node(poly::get_lower_bound(poly::as_algebraic_number(val))));
      // auto upper_c = nm->mkNode(LT, x_ran, value_to_node(poly::get_upper_bound(poly::as_algebraic_number(val))));
      // // from polynomial to constraints

      auto r = ran_to_node(poly::as_algebraic_number(val), x_ran);
      if(isMax()){
        if(isNegApprox()){
          auto c = nm->mkNode(LT, objective, x_ran).notNode();
          return nm->mkAnd(std::vector<Node>{r, c});
        }
        else{
          auto c = nm->mkNode(LEQ, objective, x_ran).notNode();
          return nm->mkAnd(std::vector<Node>{r, c});
        }
      }
      else{ // isMin()
        if(isPosApprox()){
          auto c = nm->mkNode(GT, objective, x_ran).notNode();
          return nm->mkAnd(std::vector<Node>{r, c});
        }
        else{
          auto c = nm->mkNode(GEQ, objective, x_ran).notNode();
          return nm->mkAnd(std::vector<Node>{r, c});
        }
      }
    }
    else{
      auto val_obj = obj_value_to_node(val, objective);

      if(isMax()){
        if(isNegApprox()) 
          return nm->mkNode(LT, objective, val_obj).notNode();
        else 
          return nm->mkNode(LEQ, objective, val_obj).notNode();
      }
      else{ // isMin()
        if(isPosApprox())
          return nm->mkNode(GT, objective, val_obj).notNode();
        else
          return nm->mkNode(GEQ, objective, val_obj).notNode();
      }
    }
  }
}


void objectiveValue::set_removing_sat_assignment(){
  _removing_sat_assignment = true;
}
void objectiveValue::unset_removing_sat_assignment(){
  _removing_sat_assignment = false;
}

bool objectiveValue::is_removing_sat_assignment() const{
  return _removing_sat_assignment;
}

void objectiveValue::reset(){
  _isApprox = false;
  _isPosInf = false;
  _isPosApprox = false;
  _isUnbounded = false;
}
void objectiveValue::analyze_cell(const CACInterval& characterization, const std::vector<CACInterval>& infeasibles){
  if(is_removing_sat_assignment()){
    // 2023-11-02: reset status, later ones have higher priority, because the process is reaching to optimal.
    reset();
    // anynomous author: ch is the intervals to characterize the satisfiable cell
    auto ch = characterization.d_interval;
    // auto lower = get_lower(ch);
    // auto upper = get_upper(ch);
    // std::cout<<"-----in analyze_cell-----"<<std::endl;
    // std::cout<<ch<<std::endl;
    // for(size_t i=0;i<feasibles.size();i++){
    //   std::cout<<"analyze_cell feasibles: "<<feasibles[i]<<std::endl;
    // }
    // for(size_t i=0;i<infeasibles.size();i++){
    //   std::cout<<"analyze_cell infeasibles: "<<infeasibles[i].d_interval<<std::endl;
    // }
    // std::cout<<"-----in analyze_cell-----"<<std::endl;
    // if(is_minus_infinity(lower) && is_plus_infinity(upper)){
    //   std::cout<<"Look Here !!!"<<std::endl;
    //   std::vector<poly::Interval> infeasible_intervals;
    //   for(size_t i=0;i<infeasibles.size();i++){
    //     infeasible_intervals.emplace_back(infeasibles[i].d_interval);
    //   }
    //   auto res = intervalMinus(feasibles, infeasible_intervals);
    //   std::cout<<"-----in analyze_cell {is_minus_infinity(lower) && is_plus_infinity(upper)}-----"<<std::endl;
    //   for(size_t i=0;i<res.size();i++){
    //     std::cout<<res[i]<<std::endl;
    //   }
    //   std::cout<<"-----in analyze_cell {is_minus_infinity(lower) && is_plus_infinity(upper)}-----"<<std::endl;
    //   if(res.size() == 0){
    //     // pass
    //   }
    //   else if(is_minus_infinity(get_lower(res.front())) && is_plus_infinity(get_upper(res.front()))){
    //     // 2023-09-12: removing sat assignment -> so it has a solution which is the optimal when the first (-oo, +oo)
    //     // pass
    //   }
    //   else if(isMax()){
    //     if(is_point(res.back())){
    //       // pass
    //       // it is the optimal which has stored in model
    //     }
    //     else if(is_plus_infinity(get_upper(res.back()))){
    //       // std::cout<<"unbounded +oo"<<std::endl;
    //       setPosUnbounded();
    //     }
    //     else if(get_upper_open(res.back())){
    //       // b - \epsilon
    //       setNegApprox();
    //       optApproxValue = get_upper(res.back());
    //     }
    //   }
    //   else{ // isMin()
    //     if(is_point(res.front())){
    //       // pass
    //       // it is the optimal which has stored in model
    //     }
    //     else if(is_minus_infinity(get_lower(res.front()))){
    //       // std::cout<<"unbounded -oo"<<std::endl;
    //       setNegUnbounded();
    //     }
    //     else if(get_lower_open(res.front())){
    //       // a + \epsilon 
    //       setPosApprox();
    //       optApproxValue = get_lower(res.front());
    //     }
    //   }
    // }
    // else{

    // !is_minus_infinity(lower) || !is_plus_infinity(upper)
    // ch = ch \cdot feasibles - intervals
    // it removes already unsatisfied intervals from ch and obtain a new ch
    auto real_ch = intervalIntersect(ch, feasibles);
    // std::cout<<"-----in analyze_cell {real_ch}-----"<<std::endl;
    // for(size_t i=0;i<real_ch.size();i++){
    //   std::cout<<real_ch[i]<<std::endl;
    // }
    // std::cout<<"-----in analyze_cell {real_ch}-----"<<std::endl;
    std::vector<poly::Interval> intervals;
    for(size_t i=0;i<infeasibles.size();i++){
      intervals.emplace_back(infeasibles[i].d_interval);
    }
    auto res = intervalMinus(real_ch, intervals);
    // std::cout<<"-----in analyze_cell {else}-----"<<std::endl;
    // for(size_t i=0;i<res.size();i++){
    //   std::cout<<res[i]<<std::endl;
    // }
    // std::cout<<"-----in analyze_cell {else}-----"<<std::endl;

    // if it is empty -> unsat -> find a optimal (or unsat)
    // set -oo / +oo
    if(res.size() == 0){
      // pass
    }
    else if(res.size()==1 && is_point(res.front())){
      // 2023-11-02: it is the optimal
      // pass
    }
    else if(isMax() && is_plus_infinity(get_upper(res.back()))){
      // std::cout<<"unbounded +oo"<<std::endl;
      setPosUnbounded();
    }
    else if(isMin() && is_minus_infinity(get_lower(res.front()))){
      // std::cout<<"unbounded -oo"<<std::endl;
      setNegUnbounded();
    }
    else{
      // 2023-11-01: result in an interval
      // Assert(res.size() == 1 && !is_plus_infinity(get_upper(res.front())) && !is_minus_infinity(get_lower(res.front())));
      // anynomous author: actually such assertion is ok, because -oo/+oo will never appear, as it already prune that for optimal.
      // 2023-11-02: it is res not feasibles
      if(isMax()){
        if(is_point(res.back())){
          // pass
          // it is the optimal which has stored in model
        }
        else if(is_plus_infinity(get_upper(res.back()))){
          // std::cout<<"unbounded +oo"<<std::endl;
          setPosUnbounded();
        }
        else if(get_upper_open(res.back())){
          // b - \epsilon
          setNegApprox();
          optApproxValue = get_upper(res.back());
        }
      }
      else{ // isMin()
        if(is_point(res.front())){
          // pass
          // it is the optimal which has stored in model
        }
        else if(is_minus_infinity(get_lower(res.front()))){
          // std::cout<<"unbounded -oo"<<std::endl;
          setNegUnbounded();
        }
        else if(get_lower_open(res.front())){
          // a + \epsilon 
          setPosApprox();
          optApproxValue = get_lower(res.front());
        }
      }
    }

    // }
  }
}



}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
