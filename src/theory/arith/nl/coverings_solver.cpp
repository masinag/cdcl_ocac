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
 * Implementation of new non-linear solver.
 */

#include "theory/arith/nl/coverings_solver.h"

#include "expr/skolem_manager.h"
#include "options/arith_options.h"
#include "smt/env.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/coverings/cdcac.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/arith/nl/poly_conversion.h"
#include "theory/inference_id.h"
#include "theory/theory.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

CoveringsSolver::CoveringsSolver(Env& env, InferenceManager& im, NlModel& model)
    :
      EnvObj(env),
#ifdef CVC5_POLY_IMP
      d_CAC(env),
#endif
      d_foundSatisfiability(false),
      d_im(im),
      d_model(model),
      d_eqsubs(env)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  d_ranVariable = sm->mkDummySkolem("__z", nm->realType(), "");
#ifdef CVC5_POLY_IMP
  if (env.isTheoryProofProducing())
  {
    ProofChecker* pc = env.getProofNodeManager()->getChecker();
    // add checkers
    d_proofChecker.registerTo(pc);
  }
#endif
}

CoveringsSolver::~CoveringsSolver() {}

void CoveringsSolver::initLastCall(const std::vector<Node>& assertions)
{
#ifdef CVC5_POLY_IMP
  if (TraceIsOn("nl-cov"))
  {
    Trace("nl-cov") << "CoveringsSolver::initLastCall" << std::endl;
    Trace("nl-cov") << "* Assertions: " << std::endl;
    for (const Node& a : assertions)
    {
      Trace("nl-cov") << "  " << a << std::endl;
    }
  }
  if (options().arith.nlCovVarElim)
  {
    d_eqsubs.reset();
    std::vector<Node> processed = d_eqsubs.eliminateEqualities(assertions);
    if (d_eqsubs.hasConflict())
    {
        Node lem = NodeManager::currentNM()->mkAnd(d_eqsubs.getConflict()).negate();
        d_im.addPendingLemma(lem, InferenceId::ARITH_NL_COVERING_CONFLICT, nullptr);
        Trace("nl-cov") << "Found conflict: " << lem << std::endl;
        return;
    }
    if (TraceIsOn("nl-cov"))
    {
      Trace("nl-cov") << "After simplifications" << std::endl;
      Trace("nl-cov") << "* Assertions: " << std::endl;
      for (const Node& a : processed)
      {
        Trace("nl-cov") << "  " << a << std::endl;
      }
    }
    d_CAC.reset();
    for (const Node& a : processed)
    {
      Assert(!a.isConst());
      d_CAC.getConstraints().addConstraint(a);
    }
  }
  else
  {
    d_CAC.reset();
    for (const Node& a : assertions)
    {
      Assert(!a.isConst());
      d_CAC.getConstraints().addConstraint(a);
    }
  }
  // anynomous author: TODO, compute variable ordering at this moment
  d_CAC.computeVariableOrdering();
  d_CAC.retrieveInitialAssignment(d_model, d_ranVariable);
#else
  warning() << "Tried to use CoveringsSolver but libpoly is not available. Compile "
               "with --poly."
            << std::endl;
#endif
}

void CoveringsSolver::checkFull()
{
#ifdef CVC5_POLY_IMP
  if (d_CAC.getConstraints().getConstraints().empty()) {
    d_foundSatisfiability = true;
    Trace("nl-cov") << "No constraints. Return." << std::endl;
    return;
  }
  // anynomous author: unset sat status
  d_CAC.startNewProof();
  auto covering = d_CAC.getUnsatCover();
  // check sat or optimization
  if(isOptimization()){
    if(d_CAC.isCurSAT()){
      // current branch is sat -> add incremental lemma to CDCL(T) 
      // besides we also add the negation of current constraints.
      d_foundSatisfiability = true;

      // anynomous author: TODO current it leads to an error ...
      // anynomous author: 2023-11-02: only +oo/-oo, not +epsilon/-epsilon
      if(d_CAC.isOptPosInf() || d_CAC.isOptNegInf()){
        // directly false
        Node cut = NodeManager::currentNM()->mkConst<bool>(false);
        d_im.addPendingLemma(cut, InferenceId::ARITH_NL_COVERING_EXCLUDED_INTERVAL);
      }
      else{
        // is bounded
        auto mis = collectConstraints(covering);
        // for(size_t i=0;i<covering.size();i++){
        //   std::cout<<"bounded sat intervals: "<<covering[i].d_interval<<std::endl;
        // }
        Trace("nl-cov") << "Collected MIS: " << mis << std::endl;
        Assert(!mis.empty()) << "Infeasible subset can not be empty";
        Trace("nl-cov") << "UNSAT with MIS: " << mis << std::endl;
        d_eqsubs.postprocessConflict(mis);
        Trace("nl-cov") << "After postprocessing: " << mis << std::endl;
        Node lem = NodeManager::currentNM()->mkAnd(mis).notNode();
        ProofGenerator* proof = d_CAC.closeProof(mis);
        d_im.addPendingLemma(lem, InferenceId::ARITH_NL_COVERING_CONFLICT, proof);
        // std::cout<<"error in mk increment lemma"<<std::endl;
        // std::cout<<d_CAC.objValue.mkIncrementLemma()<<std::endl;
        d_im.addPendingLemma(d_CAC.objValue.mkIncrementLemma(), InferenceId::ARITH_NL_COVERING_EXCLUDED_INTERVAL, proof);
        // std::cout<<"error in mk increment lemma, no"<<std::endl;
        // d_im.addPendingLemma(d_CAC.objValue.mkIncrementLemma(), InferenceId::ARITH_NL_COVERING_CONFLICT, proof);
        // std::cout<<"bounded sat lemma: "<<d_CAC.objValue.mkIncrementLemma()<<std::endl;
      }
    }
    else{
      // current branch is unsat -> generate lemma as usual
      d_foundSatisfiability = false;
      auto mis = collectConstraints(covering);
      // for(size_t i=0;i<covering.size();i++){
      //   std::cout<<"current branch unsat intervals: "<<covering[i].d_interval<<std::endl;
      // }
      Trace("nl-cov") << "Collected MIS: " << mis << std::endl;
      Assert(!mis.empty()) << "Infeasible subset can not be empty";
      Trace("nl-cov") << "UNSAT with MIS: " << mis << std::endl;
      d_eqsubs.postprocessConflict(mis);
      Trace("nl-cov") << "After postprocessing: " << mis << std::endl;
      Node lem = NodeManager::currentNM()->mkAnd(mis).notNode();
      ProofGenerator* proof = d_CAC.closeProof(mis);
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_COVERING_CONFLICT, proof);
      // anynomous author:remove current unsat opt assignment
      //     for example, opt = 0 -> unsat
      //     we should add a lemma: opt != 0 to forbid the branch
      // d_im.addPendingLemma(d_CAC.objValue.mkUnsatOptLemma(), InferenceId::ARITH_NL_COVERING_CONFLICT, proof);
      // std::cout<<"unsat branch lemma: "<<d_CAC.objValue.mkUnsatOptLemma()<<std::endl;
    }
  }
  else{
    if (covering.empty())
    {
      d_foundSatisfiability = true;
      // d_im.addPendingLemma(d_CAC.objValue.mkIncrementLemma(), InferenceId::ARITH_NL_COVERING_EXCLUDED_INTERVAL);
      Trace("nl-cov") << "SAT: " << d_CAC.getModel() << std::endl;
    }
    else
    {
      d_foundSatisfiability = false;
      auto mis = collectConstraints(covering);
      Trace("nl-cov") << "Collected MIS: " << mis << std::endl;
      Assert(!mis.empty()) << "Infeasible subset can not be empty";
      Trace("nl-cov") << "UNSAT with MIS: " << mis << std::endl;
      d_eqsubs.postprocessConflict(mis);
      Trace("nl-cov") << "After postprocessing: " << mis << std::endl;
      Node lem = NodeManager::currentNM()->mkAnd(mis).notNode();
      ProofGenerator* proof = d_CAC.closeProof(mis);
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_COVERING_CONFLICT, proof);
    }
  }
#else
  warning() << "Tried to use CoveringsSolver but libpoly is not available. Compile "
               "with --poly."
            << std::endl;
#endif
}

void CoveringsSolver::checkPartial()
{
#ifdef CVC5_POLY_IMP
  if (d_CAC.getConstraints().getConstraints().empty()) {
    Trace("nl-cov") << "No constraints. Return." << std::endl;
    return;
  }
  auto covering = d_CAC.getUnsatCover(true);
  // if (covering.empty() || (isOptimization() && d_CAC.isOptSAT()))
  // if(isOptimization()){
  //   if(d_CAC.isCurSAT()){
  //     // current branch is sat -> add incremental lemma to CDCL(T) 
  //     // besides we also add the negation of current constraints.
  //     d_foundSatisfiability = true;

  //     // anynomous author: TODO current it leads to an error ...
  //     if(d_CAC.isOptUnbounded()){
  //       // directly false
  //       Node cut = NodeManager::currentNM()->mkConst<bool>(false);
  //       d_im.addPendingLemma(cut, InferenceId::ARITH_NL_COVERING_EXCLUDED_INTERVAL);
  //     }
  //     else{
  //       // is not unbounded
  //       auto mis = collectConstraints(covering);
  //       Trace("nl-cov") << "Collected MIS: " << mis << std::endl;
  //       Assert(!mis.empty()) << "Infeasible subset can not be empty";
  //       Trace("nl-cov") << "UNSAT with MIS: " << mis << std::endl;
  //       d_eqsubs.postprocessConflict(mis);
  //       Trace("nl-cov") << "After postprocessing: " << mis << std::endl;
  //       Node lem = NodeManager::currentNM()->mkAnd(mis).notNode();
  //       ProofGenerator* proof = d_CAC.closeProof(mis);
  //       d_im.addPendingLemma(lem, InferenceId::ARITH_NL_COVERING_CONFLICT, proof);
  //       // std::cout<<d_CAC.objValue.mkIncrementLemma()<<std::endl;
  //       d_im.addPendingLemma(d_CAC.objValue.mkIncrementLemma(), InferenceId::ARITH_NL_COVERING_EXCLUDED_INTERVAL, proof);
  //     }
  //   }
  //   else{
  //     // current branch is unsat -> generate lemma as usual
  //     d_foundSatisfiability = false;
  //     auto mis = collectConstraints(covering);
  //     Trace("nl-cov") << "Collected MIS: " << mis << std::endl;
  //     Assert(!mis.empty()) << "Infeasible subset can not be empty";
  //     Trace("nl-cov") << "UNSAT with MIS: " << mis << std::endl;
  //     d_eqsubs.postprocessConflict(mis);
  //     Trace("nl-cov") << "After postprocessing: " << mis << std::endl;
  //     Node lem = NodeManager::currentNM()->mkAnd(mis).notNode();
  //     ProofGenerator* proof = d_CAC.closeProof(mis);
  //     d_im.addPendingLemma(lem, InferenceId::ARITH_NL_COVERING_CONFLICT, proof);
  //   }
  // }
  // else{
  if (covering.empty())
  {
    d_foundSatisfiability = true;
    Trace("nl-cov") << "SAT: " << d_CAC.getModel() << std::endl;
  }
  else
  {
    auto* nm = NodeManager::currentNM();
    Node first_var =
        d_CAC.getConstraints().varMapper()(d_CAC.getVariableOrdering()[0]);
    for (const auto& interval : covering)
    {
      Node premise;
      Assert(!interval.d_origins.empty());
      if (interval.d_origins.size() == 1)
      {
        premise = interval.d_origins[0];
      }
      else
      {
        premise = nm->mkNode(Kind::AND, interval.d_origins);
      }
      Node conclusion =
          excluding_interval_to_lemma(first_var, interval.d_interval, false);
      if (!conclusion.isNull())
      {
        Node lemma = nm->mkNode(Kind::IMPLIES, premise, conclusion);
        Trace("nl-cov") << "Excluding " << first_var << " -> "
                        << interval.d_interval << " using " << lemma
                        << std::endl;
        d_im.addPendingLemma(lemma,
                            InferenceId::ARITH_NL_COVERING_EXCLUDED_INTERVAL);
      }
    }
  }
  // }
#else
  warning() << "Tried to use CoveringsSolver but libpoly is not available. Compile "
               "with --poly."
            << std::endl;
#endif
}

bool CoveringsSolver::constructModelIfAvailable(std::vector<Node>& assertions)
{
#ifdef CVC5_POLY_IMP
  if (!d_foundSatisfiability)
  {
    return false;
  }
  bool foundNonVariable = false;
  for (const auto& v : d_CAC.getVariableOrdering())
  {
    Node variable = d_CAC.getConstraints().varMapper()(v);
    if (!Theory::isLeafOf(variable, TheoryId::THEORY_ARITH))
    {
      Trace("nl-cov") << "Not a variable: " << variable << std::endl;
      foundNonVariable = true;
    }
    Node value;
    value = value_to_node(d_CAC.getModel().get(v), variable);
    // std::cout<<variable<<" "<<value<<std::endl;
    addToModel(variable, value);
  }
  for (const auto& sub : d_eqsubs.getSubstitutions())
  {
    Trace("nl-cov") << "EqSubs: " << sub.first << " -> " << sub.second
                    << std::endl;
    addToModel(sub.first, sub.second);
  }
  if (foundNonVariable)
  {
    Trace("nl-cov")
        << "Some variable was an extended term, don't clear list of assertions."
        << std::endl;
    return false;
  }
  Trace("nl-cov") << "Constructed a full assignment, clear list of assertions."
                  << std::endl;
  assertions.clear();
  return true;
#else
  warning() << "Tried to use CoveringsSolver but libpoly is not available. Compile "
               "with --poly."
            << std::endl;
  return false;
#endif
}

void CoveringsSolver::addToModel(TNode var, TNode value) const
{
  Assert(value.getType().isRealOrInt());
  // we must take its substituted form here, since other solvers (e.g. the
  // reductions inference of the sine solver) may have introduced substitutions
  // internally during check.
  Node svalue = d_model.getSubstitutedForm(value);
  // ensure the value has integer type if var has integer type
  if (var.getType().isInteger())
  {
    if (svalue.getKind() == Kind::TO_REAL)
    {
      svalue = svalue[0];
    }
    else if (svalue.getKind() == Kind::CONST_RATIONAL)
    {
      Assert(svalue.getConst<Rational>().isIntegral());
      svalue =
          NodeManager::currentNM()->mkConstInt(svalue.getConst<Rational>());
    }
  }
  Trace("nl-cov") << "-> " << var << " = " << svalue << std::endl;
  d_model.addSubstitution(var, svalue);
}

// anynomous author: optimization

bool CoveringsSolver::isOptimization() const{
  return _isOptimization != OPT_TYPE::NON_OPT;
}
void CoveringsSolver::setOptimization(){
  _isOptimization = OPT_TYPE::WAITING;
  // std::cout<<"CoveringsSolver::setOptimization"<<std::endl;
  d_CAC.setOptimization();
}
void CoveringsSolver::setObjective(OPT_TYPE _isOpt, Node& e){
  // std::cout<<"CoveringsSolver::setObjective"<<std::endl;
  _isOptimization = _isOpt;
  d_CAC.setObjective(_isOpt, e);
}
void CoveringsSolver::assertOptBound(){
  d_CAC.assertOptBound();
}
bool CoveringsSolver::missBound() const{
  return getBoundValue(objectiveVariable) != getOptimizedValue(objectiveVariable);
}
Node CoveringsSolver::getBoundValue(const Node& e) const{
  return d_CAC.getOptimizedValue(e);
}
Node CoveringsSolver::getOptimizedValue(const Node& e) const{
  return d_CAC.getOptimizedValue(e);
}
bool CoveringsSolver::isOptSAT() const{
  return d_CAC.isOptSAT();
}
void CoveringsSolver::getOptModelCache(std::map<Node, Node>& optCache){
  d_CAC.getOptModelCache(optCache);
}

bool CoveringsSolver::isOptUnbounded() const{
  return d_CAC.isOptUnbounded();
}
bool CoveringsSolver::isOptPosInf() const{
  return d_CAC.isOptPosInf();
}
bool CoveringsSolver::isOptNegInf() const{
  return d_CAC.isOptNegInf();
}
bool CoveringsSolver::isOptPosApprox() const{
  return d_CAC.isOptPosApprox();
}
bool CoveringsSolver::isOptNegApprox() const{
  return d_CAC.isOptNegApprox();
}


}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
