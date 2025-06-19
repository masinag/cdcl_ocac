/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements utilities for cdcac.
 */

#include "theory/arith/nl/coverings/cdcac_utils.h"

#ifdef CVC5_POLY_IMP

#include <optional>

#include "theory/arith/nl/coverings/projections.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace coverings {

using namespace poly;

bool operator==(const CACInterval& lhs, const CACInterval& rhs)
{
  return lhs.d_interval == rhs.d_interval;
}
bool operator<(const CACInterval& lhs, const CACInterval& rhs)
{
  return lhs.d_interval < rhs.d_interval;
}

namespace {
/**
 * Induces an ordering on poly intervals that is suitable for redundancy
 * removal as implemented in clean_intervals.
 */
bool compareForCleanup(const Interval& lhs, const Interval& rhs)
{
  const lp_value_t* ll = &(lhs.get_internal()->a);
  const lp_value_t* lu =
      lhs.get_internal()->is_point ? ll : &(lhs.get_internal()->b);
  const lp_value_t* rl = &(rhs.get_internal()->a);
  const lp_value_t* ru =
      rhs.get_internal()->is_point ? rl : &(rhs.get_internal()->b);

  int lc = lp_value_cmp(ll, rl);
  // Lower bound is smaller
  if (lc < 0) return true;
  // Lower bound is larger
  if (lc > 0) return false;
  // Lower bound type is smaller
  if (!lhs.get_internal()->a_open && rhs.get_internal()->a_open) return true;
  // Lower bound type is larger
  if (lhs.get_internal()->a_open && !rhs.get_internal()->a_open) return false;

  // Attention: Here it differs from the regular interval ordering!
  int uc = lp_value_cmp(lu, ru);
  // Upper bound is smaller
  if (uc < 0) return false;
  // Upper bound is larger
  if (uc > 0) return true;
  // Upper bound type is smaller
  if (lhs.get_internal()->b_open && !rhs.get_internal()->b_open) return false;
  // Upper bound type is larger
  if (!lhs.get_internal()->b_open && rhs.get_internal()->b_open) return true;

  // Identical
  return false;
}

/**
 * Check whether lhs covers rhs.
 */
bool intervalCovers(const Interval& lhs, const Interval& rhs)
{
  const lp_value_t* ll = &(lhs.get_internal()->a);
  const lp_value_t* lu =
      lhs.get_internal()->is_point ? ll : &(lhs.get_internal()->b);
  const lp_value_t* rl = &(rhs.get_internal()->a);
  const lp_value_t* ru =
      rhs.get_internal()->is_point ? rl : &(rhs.get_internal()->b);

  int lc = lp_value_cmp(ll, rl);
  int uc = lp_value_cmp(lu, ru);

  // Lower bound is smaller and upper bound is larger
  if (lc < 0 && uc > 0) return true;
  // Lower bound is larger or upper bound is smaller
  if (lc > 0 || uc < 0) return false;

  // Now both bounds are identical.
  Assert(lc <= 0 && uc >= 0);
  Assert(lc == 0 || uc == 0);

  // Lower bound is the same and the bound type is stricter
  if (lc == 0 && lhs.get_internal()->a_open && !rhs.get_internal()->a_open)
    return false;
  // Upper bound is the same and the bound type is stricter
  if (uc == 0 && lhs.get_internal()->b_open && !rhs.get_internal()->b_open)
    return false;

  // Both bounds are weaker
  return true;
}

/**
 * Check whether two intervals connect, assuming lhs < rhs.
 * They connect, if their union has no gap.
 */
bool intervalConnect(const Interval& lhs, const Interval& rhs)
{
  Assert(lhs < rhs) << "Can only check for a connection if lhs < rhs.";

  const lp_value_t* lu = poly::get_upper(lhs).get_internal();
  const lp_value_t* rl = poly::get_lower(rhs).get_internal();
  
  int c = lp_value_cmp(lu, rl);
  // std::cout<<poly::get_upper(lhs)<<" "<<poly::get_lower(rhs)<<" "<<c<<std::endl;
  if (c < 0)
  {
    Trace("libpoly::interval_connect")
        << lhs << " and " << rhs << " are separated." << std::endl;
    return false;
  }
  if (c > 0)
  {
    Trace("libpoly::interval_connect")
        << lhs << " and " << rhs << " overlap." << std::endl;
    return true;
  }
  Assert(c == 0);
  if (poly::get_upper_open(lhs) && poly::get_lower_open(rhs))
  {
    Trace("libpoly::interval_connect")
        << lhs << " and " << rhs
        << " touch and the intermediate point is not covered." << std::endl;
    return false;
  }
  Trace("libpoly::interval_connect")
      << lhs << " and " << rhs
      << " touch and the intermediate point is covered." << std::endl;
  return true;
}

/**
 * Check whether the union of a and b covers rhs.
 * First check whether a and b connect, and then defer the containment check to
 * intervalCovers.
 */
std::optional<bool> intervalsCover(const Interval& a,
                                   const Interval& b,
                                   const Interval& rhs)
{
  if (!intervalConnect(a, b)) return {};

  Interval c(poly::get_lower(a),
             poly::get_lower_open(a),
             poly::get_upper(b),
             poly::get_upper_open(b));

  return intervalCovers(c, rhs);
}
}  // namespace

void cleanIntervals(std::vector<CACInterval>& intervals)
{
  // Simplifies removal of redundancies later on.
  if (intervals.size() < 2) return;

  if (TraceIsOn("cdcac"))
  {
    Trace("cdcac") << "Before pruning:" << std::endl;
    for (const auto& i : intervals)
    {
      Trace("cdcac") << "\t[" << i.d_id << "] " << i.d_interval << std::endl;
    }
  }

  // Sort intervals.
  std::sort(intervals.begin(),
            intervals.end(),
            [](const CACInterval& lhs, const CACInterval& rhs) {
              return compareForCleanup(lhs.d_interval, rhs.d_interval);
            });

  // First remove intervals that are completely covered by a single other
  // interval. This corresponds to removing "redundancies of the first kind" as
  // of 4.5.1 The implementation roughly follows
  // https://en.cppreference.com/w/cpp/algorithm/remove
  std::size_t first = 0;
  // Find first interval that is covered.
  for (std::size_t n = intervals.size(); first < n - 1; ++first)
  {
    if (intervalCovers(intervals[first].d_interval,
                       intervals[first + 1].d_interval))
    {
      break;
    }
  }
  // If such an interval exists, remove accordingly.
  if (first < intervals.size() - 1)
  {
    for (std::size_t i = first + 2, n = intervals.size(); i < n; ++i)
    {
      if (!intervalCovers(intervals[first].d_interval, intervals[i].d_interval))
      {
        // Interval is not covered. Move it to the front and bump front.
        ++first;
        intervals[first] = std::move(intervals[i]);
      }
      // Else: Interval is covered as well.
    }
    // Erase trailing values
    while (intervals.size() > first + 1)
    {
      intervals.pop_back();
    }
  }
  if (TraceIsOn("cdcac"))
  {
    Trace("cdcac") << "After pruning:" << std::endl;
    for (const auto& i : intervals)
    {
      Trace("cdcac") << "\t[" << i.d_id << "] " << i.d_interval << std::endl;
    }
  }
}

void removeRedundantIntervals(std::vector<CACInterval>& intervals)
{
  // mid-1 -> interval below
  // mid   -> current interval
  // right -> interval above
  size_t mid = 1;
  size_t right = 2;
  size_t n = intervals.size();
  while (right < n)
  {
    bool found = false;
    for (size_t r = right; r < n; ++r)
    {
      const auto& below = intervals[mid - 1].d_interval;
      const auto& middle = intervals[mid].d_interval;
      const auto& above = intervals[r].d_interval;
      if (intervalsCover(below, above, middle))
      {
        found = true;
        break;
      }
    }
    if (found)
    {
      intervals[mid] = std::move(intervals[right]);
    }
    else
    {
      ++mid;
      if (mid < right)
      {
        intervals[mid] = std::move(intervals[right]);
      }
    }
    ++right;
  }
  while (intervals.size() > mid + 1)
  {
    intervals.pop_back();
  }
}

std::vector<Node> collectConstraints(const std::vector<CACInterval>& intervals)
{
  std::vector<Node> res;
  for (const auto& i : intervals)
  {
    res.insert(res.end(), i.d_origins.begin(), i.d_origins.end());
  }
  std::sort(res.begin(), res.end());
  auto it = std::unique(res.begin(), res.end());
  res.erase(it, res.end());
  return res;
}

bool sampleOutside(const std::vector<CACInterval>& infeasible, Value& sample)
{
  if (infeasible.empty())
  {
    // No infeasible region, just take anything: zero
    sample = poly::Integer();
    return true;
  }
  if (!is_minus_infinity(get_lower(infeasible.front().d_interval)))
  {
    // First does not cover -oo, just take sufficiently low value
    Trace("cdcac") << "Sample before " << infeasible.front().d_interval
                   << std::endl;
    const auto* i = infeasible.front().d_interval.get_internal();
    sample = value_between(
        Value::minus_infty().get_internal(), true, &i->a, !i->a_open);
    return true;
  }
  for (std::size_t i = 0, n = infeasible.size(); i < n - 1; ++i)
  {
    // Search for two subsequent intervals that do not connect
    if (!intervalConnect(infeasible[i].d_interval,
                         infeasible[i + 1].d_interval))
    {
      // Two intervals do not connect, take something from the gap
      const auto* l = infeasible[i].d_interval.get_internal();
      const auto* r = infeasible[i + 1].d_interval.get_internal();

      Trace("cdcac") << "Sample between " << infeasible[i].d_interval << " and "
                     << infeasible[i + 1].d_interval << std::endl;

      if (l->is_point)
      {
        sample = value_between(&l->a, true, &r->a, !r->a_open);
      }
      else
      {
        sample = value_between(&l->b, !l->b_open, &r->a, !r->a_open);
      }
      return true;
    }
    else
    {
      Trace("cdcac") << infeasible[i].d_interval << " and "
                     << infeasible[i + 1].d_interval << " connect" << std::endl;
    }
  }
  if (!is_plus_infinity(get_upper(infeasible.back().d_interval)))
  {
    // Last does not cover oo, just take something sufficiently large
    Trace("cdcac") << "Sample above " << infeasible.back().d_interval
                   << std::endl;
    const auto* i = infeasible.back().d_interval.get_internal();
    if (i->is_point)
    {
      sample =
          value_between(&i->a, true, Value::plus_infty().get_internal(), true);
    }
    else
    {
      sample = value_between(
          &i->b, !i->b_open, Value::plus_infty().get_internal(), true);
    }
    return true;
  }
  return false;
}

// anynomous author: optimization sample function
bool sampleOutsidewithDirection(const std::vector<CACInterval>& infeasible, Value& sample, bool isMinimize){
  if (infeasible.empty())
  {
    // No infeasible region, just take anything: zero
    sample = poly::Integer();
    return true;
  }
  // for (std::size_t i = 0, n = infeasible.size(); i < n; ++i)
  // {
  //   std::cout<<"sampleOutsidewithDirection: "<<i<<" "<<infeasible[i].d_interval<<std::endl;
  // }
  if(isMinimize){
    // minimize -> from 0 to n - 1
    if (!is_minus_infinity(get_lower(infeasible.front().d_interval)))
    {
      // First does not cover -oo, just take sufficiently low value
      Trace("cdcac") << "Sample before " << infeasible.front().d_interval
                    << std::endl;
      const auto* i = infeasible.front().d_interval.get_internal();
      sample = value_between(
          Value::minus_infty().get_internal(), true, &i->a, !i->a_open);
      return true;
    }
    for (std::size_t i = 0, n = infeasible.size(); i < n - 1; ++i)
    {
      // Search for two subsequent intervals that do not connect
      if (!intervalConnect(infeasible[i].d_interval,
                          infeasible[i + 1].d_interval))
      {
        // Two intervals do not connect, take something from the gap
        const auto* l = infeasible[i].d_interval.get_internal();
        const auto* r = infeasible[i + 1].d_interval.get_internal();

        Trace("cdcac") << "Sample between " << infeasible[i].d_interval << " and "
                      << infeasible[i + 1].d_interval << std::endl;
        if (l->is_point)
        {
          // TODO, it is important branch, for example, l = [3/2, 3/2] but in implemetation it is [3/2, +oo) with b_inf = true...
          sample = value_between(&l->a, true, &r->a, !r->a_open);
        }
        else if (l->b_open){
          // anynomous author: 2023-08-16: (-oo, 3/2) -> sample 3/2 first
          sample = value_between(&l->b, false, &l->b, false);
        }
        else
        {
          sample = value_between(&l->b, !l->b_open, &r->a, !r->a_open);
        }
        Trace("cdcac") << "Sample between " << infeasible[i].d_interval << " and "
                      << infeasible[i + 1].d_interval << std::endl;
        return true;
      }
      else
      {
        Trace("cdcac") << infeasible[i].d_interval << " and "
                      << infeasible[i + 1].d_interval << " connect" << std::endl;
      }
    }
    if (!is_plus_infinity(get_upper(infeasible.back().d_interval)))
    {
      // Last does not cover oo, just take something sufficiently large
      Trace("cdcac") << "Sample above " << infeasible.back().d_interval
                    << std::endl;
      const auto* i = infeasible.back().d_interval.get_internal();
      if (i->is_point){
        // TODO, it is important branch, for example, l = [3/2, 3/2] but in implemetation it is [3/2, +oo) with b_inf = true...
        sample = value_between(&i->a, true, Value::plus_infty().get_internal(), true);
      }
      else if (i->b_open){
        // anynomous author: 2023-08-16: (0, 3/2) -> sample 3/2 first
        sample = value_between(&i->b, false, &i->b, false);
      }
      else
      {
        sample = value_between(
            &i->b, !i->b_open, Value::plus_infty().get_internal(), true);
      }
      return true;
    }
    return false;
  }
  else{
    // maximize -> from n - 1 to 0
    if (!is_plus_infinity(get_upper(infeasible.back().d_interval)))
    {
      // Last does not cover oo, just take something sufficiently large
      Trace("cdcac") << "Sample above " << infeasible.back().d_interval
                    << std::endl;
      const auto* i = infeasible.back().d_interval.get_internal();
      sample = value_between(
          &i->b, !i->b_open, Value::plus_infty().get_internal(), true);
      return true;
    }
    for (std::size_t i = infeasible.size()-1; i > 0; --i)
    {
      // Search for two subsequent intervals that do not connect
      if (!intervalConnect(infeasible[i - 1].d_interval,
                          infeasible[i].d_interval))
      {
        // Two intervals do not connect, take something from the gap
        const auto* l = infeasible[i - 1].d_interval.get_internal();
        const auto* r = infeasible[i].d_interval.get_internal();

        Trace("cdcac") << "Sample between " << infeasible[i - 1].d_interval << " and "
                      << infeasible[i].d_interval << std::endl;
        if (l->is_point){
          // TODO, it is important branch, for example, l = [3/2, 3/2] but in implemetation it is [3/2, +oo) with b_inf = true...
          sample = value_between(&l->a, true, &r->a, !r->a_open);
        }
        else if (r->a_open){
          // anynomous author: 2023-08-16: (3/2, +oo) -> sample 3/2 first
          sample = value_between(&r->a, false, &r->a, false);
        }
        else
        {
          sample = value_between(&l->b, !l->b_open, &r->a, !r->a_open);
        }
        return true;
      }
      else
      {
        Trace("cdcac") << infeasible[i - 1].d_interval << " and "
                      << infeasible[i].d_interval << " connect" << std::endl;
      }
    }
    if (!is_minus_infinity(get_lower(infeasible.front().d_interval)))
    {
      // First does not cover -oo, just take sufficiently low value
      Trace("cdcac") << "Sample before " << infeasible.front().d_interval
                    << std::endl;
      const auto* i = infeasible.front().d_interval.get_internal();
      if(i->a_open){
        // anynomous author: 2023-08-16: (3/2, 6) -> sample 3/2 first
        sample = value_between(&i->a, false, &i->a, false);
      }
      else{
        sample = value_between(
            Value::minus_infty().get_internal(), true, &i->a, !i->a_open);
      }
      return true;
    }
    return false;
  }
}



namespace {
/**
 * Replace a polynomial at polys[id] with the given pair of polynomials.
 * Also update d_mainPolys in the given interval accordingly.
 * If one of the factors (from the pair) is from a lower level (has a different
 * main variable), push this factor to the d_downPolys.
 * The first factor needs to be a proper polynomial (!is_constant(subst.first)),
 * but the second factor may be anything.
 */
void replace_polynomial(PolyVector& polys,
                        std::size_t id,
                        std::pair<poly::Polynomial, poly::Polynomial> subst,
                        CACInterval& interval)
{
  Assert(polys[id] == subst.first * subst.second);
  Assert(!is_constant(subst.first));
  // Whether polys[id] has already been replaced
  bool replaced = false;
  poly::Variable var = main_variable(polys[id]);
  // The position within interval.d_mainPolys to be replaced.
  auto mit = std::find(
      interval.d_mainPolys.begin(), interval.d_mainPolys.end(), polys[id]);
  if (main_variable(subst.first) == var)
  {
    // Replace in polys[id] and *mit
    polys[id] = subst.first;
    if (mit != interval.d_mainPolys.end())
    {
      *mit = subst.first;
    }
    replaced = true;
  }
  else
  {
    // Push to d_downPolys
    interval.d_downPolys.add(subst.first);
  }
  // Skip constant poly
  if (!is_constant(subst.second))
  {
    if (main_variable(subst.second) == var)
    {
      if (replaced)
      {
        // Append to polys and d_mainPolys
        polys.add(subst.second);
        interval.d_mainPolys.add(subst.second);
      }
      else
      {
        // Replace in polys[id] and *mit
        polys[id] = subst.second;
        if (mit != interval.d_mainPolys.end())
        {
          *mit = subst.second;
        }
        replaced = true;
      }
    }
    else
    {
      // Push to d_downPolys
      interval.d_downPolys.add(subst.second);
    }
  }
  Assert(replaced)
      << "At least one of the factors should have the main variable";
}
}  // namespace

void makeFinestSquareFreeBasis(CACInterval& lhs, CACInterval& rhs)
{
  auto& l = lhs.d_upperPolys;
  auto& r = rhs.d_lowerPolys;
  if (l.empty()) return;
  for (std::size_t i = 0, ln = l.size(); i < ln; ++i)
  {
    for (std::size_t j = 0, rn = r.size(); j < rn; ++j)
    {
      // All main variables should be the same
      Assert(main_variable(l[i]) == main_variable(r[j]));
      if (l[i] == r[j]) continue;
      Polynomial g = gcd(l[i], r[j]);
      if (!is_constant(g))
      {
        auto newl = div(l[i], g);
        auto newr = div(r[j], g);
        replace_polynomial(l, i, std::make_pair(g, newl), lhs);
        replace_polynomial(r, j, std::make_pair(g, newr), rhs);
      }
    }
  }
  l.reduce();
  r.reduce();
  lhs.d_mainPolys.reduce();
  rhs.d_mainPolys.reduce();
  lhs.d_downPolys.reduce();
  rhs.d_downPolys.reduce();
}

bool checkUnbounded(const std::vector<CACInterval>& infeasible, Interval& proof){
  if (infeasible.empty()) return false;
  int interval_cnt = 0;
  if (!is_minus_infinity(get_lower(infeasible.front().d_interval))) interval_cnt += 1;
  if (!is_plus_infinity(get_upper(infeasible.back().d_interval))) interval_cnt += 1;
  if (interval_cnt >= 2) return false; // (-oo, a) (b, +oo)
  Interval tmp;
  for (std::size_t i = 0, n = infeasible.size(); i+1 < n; ++i){
    const auto l = infeasible[i].d_interval; // no need to get_internal
    const auto r = infeasible[i + 1].d_interval;
    if (!intervalConnect(infeasible[i].d_interval, infeasible[i + 1].d_interval)){
      // Two intervals do not connect, take something from the gap
      if(is_point(l)){
        // if(r->is_point) // no need // a_open is always valid
        if(get_lower_open(r)) return false; // [a, a] (b, ?) contains [b], (a, b) two cells
        interval_cnt += 1;
        if(interval_cnt >= 2) return false;
        tmp = Interval(get_upper(l), true, get_lower(r), true);
      }
      else{
        if(get_upper_open(l) && get_lower_open(r)){
          int lc = (get_upper(l) == get_lower(r));
          if (lc == 0){ // (l_a, l_b) (r_a, r_b) and l_b == r_a -> [l_b, l_b] only one cell
            interval_cnt += 1;
            if(interval_cnt >= 2) return false;
            tmp = Interval(get_upper(l), true, get_lower(r), true);
          }
        }
        if(get_upper_open(l)) return false; // (a, b) contains [b], (b, ?) two cells
        if(get_lower_open(r)) return false; // (a, b) contains [a], (?, a) two cells
        interval_cnt += 1;
        if(interval_cnt >= 2) return false;
        else{
          // assert(!l->b_open && !r->a_open);
          // it is the first only one interval
          tmp = Interval(get_upper(l), true, get_lower(r), true);
        }
      }
    }
    else{
      // the last connected pairs
      if(i+1==n-1 && is_point(r) && get_upper(l) == get_lower(r)){
        // (-inf, 3/2) + [3/2]
        tmp = Interval(get_upper(l), true, get_lower(r), true);
      }
    }
  }
  if(interval_cnt >= 2) return false;
  else{
    proof = tmp;
    return true;
  }
}


void cleanIntervals(std::vector<Interval>& intervals)
{
  // Simplifies removal of redundancies later on.
  if (intervals.size() < 2) return;

  if (TraceIsOn("cdcac"))
  {
    Trace("cdcac") << "Before pruning:" << std::endl;
    for (const auto& i : intervals)
    {
      Trace("cdcac") << "\t" << i << std::endl;
    }
  }

  // Sort intervals.
  std::sort(intervals.begin(),
            intervals.end(),
            compareForCleanup);

  // First remove intervals that are completely covered by a single other
  // interval. This corresponds to removing "redundancies of the first kind" as
  // of 4.5.1 The implementation roughly follows
  // https://en.cppreference.com/w/cpp/algorithm/remove
  std::size_t first = 0;
  // Find first interval that is covered.
  for (std::size_t n = intervals.size(); first < n - 1; ++first)
  {
    if (intervalCovers(intervals[first],
                       intervals[first + 1]))
    {
      break;
    }
  }
  // If such an interval exists, remove accordingly.
  if (first < intervals.size() - 1)
  {
    for (std::size_t i = first + 2, n = intervals.size(); i < n; ++i)
    {
      if (!intervalCovers(intervals[first], intervals[i]))
      {
        // Interval is not covered. Move it to the front and bump front.
        ++first;
        intervals[first] = std::move(intervals[i]);
      }
      // Else: Interval is covered as well.
    }
    // Erase trailing values
    while (intervals.size() > first + 1)
    {
      intervals.pop_back();
    }
  }
  if (TraceIsOn("cdcac"))
  {
    Trace("cdcac") << "After pruning:" << std::endl;
    for (const auto& i : intervals)
    {
      Trace("cdcac") << "\t" << i << std::endl;
    }
  }
}
std::vector<Interval> intervalMinus(const Interval& a, const Interval& b){
  std::vector<Interval> res;
  // 2023-09-17: intervalConnect must a<b -> a<b?intervalConnect(a, b):intervalConnect(b, a)
  if(a<b?intervalConnect(a, b):intervalConnect(b, a)){
    if(is_point(a) && is_point(b)){
      if(get_lower(a) == get_lower(b)){
        return res;
      }
      else{
        // nothing to do
        res.emplace_back(a);
      }
    }
    else if(is_point(a)){
      // !is_point(b)
      if(contains(b, get_lower(a))){
        return res;
      }
      else{
        res.emplace_back(a);
      }
    }
    else if(is_point(b)){
      // !is_point(a)
      if(contains(a, get_lower(b))){
        // split
        auto lower = get_lower(a);
        auto upper = get_upper(a);
        auto s     = get_lower(b);

        if(lower == s){
          if(get_lower_open(a)){
            res.emplace_back(a);
          }
          else{
            res.emplace_back(Interval(lower, true, upper, get_upper_open(a)));
          }
        }
        else if(upper == s){
          if(get_upper_open(a)){
            res.emplace_back(a);
          }
          else{
            res.emplace_back(Interval(lower, get_lower_open(a), upper, true));
          }
        }
        else{
          // lower != s && upper != s
          // 
          res.emplace_back(Interval(lower, get_lower_open(a), s, true));
          res.emplace_back(Interval(s, true, upper, get_upper_open(a)));
        }
      }
      else{
        res.emplace_back(a);
      }
    }
    else{
      // std::cout<<a<<" "<<b<<std::endl;
      // !is_point(a) && !is_point(b)
      if(intervalCovers(b, a)){
        // a:   (  )
        // b: (      )
        // std::cout<<"1"<<std::endl;
        return res;
      }
      else if(intervalCovers(a, b)){
        // a: (      )
        // b:   (  )
        // std::cout<<"2"<<std::endl;
        // anynomous author: impossible
        // ( )
        // ( )
        if(get_lower(a) == get_lower(b) && get_upper(a) == get_upper(b) && !get_lower_open(a) && get_lower_open(b)){
          // 2023-09-16: as not cover, it is enough.
          // std::cout<<"3"<<std::endl;
          res.emplace_back(Interval(get_lower(a), false, get_lower(a), false));
        }
        else if(get_lower(a) == get_lower(b) && get_upper(a) == get_upper(b) && !get_upper_open(a) && get_upper_open(b)){
          // std::cout<<"4"<<std::endl;
          res.emplace_back(Interval(get_upper(a), false, get_upper(a), false));
        }
        else if(get_lower(a) == get_lower(b) && get_lower_open(a) && get_lower_open(b)){
          // std::cout<<"7"<<std::endl;
          res.emplace_back(Interval(get_upper(b), !get_upper_open(b), get_upper(a), get_upper_open(a)));
        }
        else if(get_upper(a) == get_upper(b) && get_upper_open(a) && get_upper_open(b)){
          // std::cout<<"8"<<std::endl;
          res.emplace_back(Interval(get_lower(a), get_lower_open(a), get_lower(b), !get_lower_open(b)));
        }
        else{
          if(!is_minus_infinity(get_lower(b))) res.emplace_back(Interval(get_lower(a), get_lower_open(a), get_lower(b), !get_lower_open(b)));
          if(!is_plus_infinity(get_upper(b))) res.emplace_back(Interval(get_upper(b), !get_upper_open(b), get_upper(a), get_upper_open(a)));
        }
      }
      // else if(get_upper(a) == get_upper(b) && !get_upper_open(a) && get_upper_open(b)){
      //   // 2023-09-16: as not cover, it is enough.
      //   std::cout<<"3"<<std::endl;
      //   res.emplace_back(Interval(get_upper(a), false, get_upper(a), false));
      // }
      // else if(get_lower(a) == get_lower(b) && !get_lower_open(a) && get_lower_open(b)){
      //   std::cout<<"4"<<std::endl;
      //   res.emplace_back(Interval(get_lower(a), false, get_lower(a), false));
      // }
      else if(get_upper(a) >= get_lower(b) && get_upper(a) <= get_upper(b)){
        // a: (  )
        // b:   (  )
        // std::cout<<"5"<<std::endl;
        res.emplace_back(Interval(get_lower(a), get_lower_open(a), get_lower(b), !get_lower_open(b)));
      }
      else if(get_upper(b) >= get_lower(a) && get_lower(b) <= get_lower(a)){
        // a:   (  )
        // b: (  )
        // std::cout<<"7"<<std::endl;
        res.emplace_back(Interval(get_upper(b), !get_upper_open(b), get_upper(a), get_upper_open(a)));
      }
      else{
        std::cout<<a<<"-"<<b<<std::endl;
        Assert(false);
      }
    }
  }
  else{
    res.emplace_back(a);
  }

  cleanIntervals(res);
  return res;
}
std::vector<Interval> intervalMinus(const std::vector<Interval>& a, const Interval& b){
  std::vector<Interval> res;
  for(size_t i=0;i<a.size();i++){
    auto tres = intervalMinus(a[i], b);
    res.insert(res.end(), tres.begin(), tres.end());
  }
  cleanIntervals(res);
  return res;
}
std::vector<Interval> intervalMinus(const Interval& a, const std::vector<Interval>& b){
  std::vector<Interval> res;
  res.emplace_back(a);
  for(size_t j=0;j<b.size();j++){
    res = intervalMinus(res, b[j]);
  }
  cleanIntervals(res);
  return res;
}
std::vector<poly::Interval> intervalMinus(const std::vector<poly::Interval>& a, const std::vector<poly::Interval>& b){
  std::vector<Interval> res;
  for(size_t i=0;i<a.size();i++){
    std::vector<Interval> tres;
    tres.emplace_back(a[i]);
    bool empty = false;
    for(size_t j=0;j<b.size();j++){
      auto ttres = intervalMinus(tres, b[j]);
      if(ttres.size() == 0){
        empty = true;
        break;
      }
      tres.clear();
      tres.insert(tres.end(), ttres.begin(), ttres.end());
    }
    if(!empty) res.insert(res.end(), tres.begin(), tres.end());
  }
  cleanIntervals(res);
  return res;
}

std::vector<poly::Interval> intervalIntersect(const poly::Interval& a, const poly::Interval& b){

  // 2023-11-03: must connect, else empty.
  // anynomous author: from CVC5 implementation:
  // Basic idea to organize this function:
  // The bounds for res have 5 positions:
  // 1 < 2 (lower(cur)) < 3 < 4 (upper(cur)) < 5
  poly::Interval cur(a);
  poly::Interval res(b);
  if (get_upper(res) < get_lower(cur))
  {
    // upper(res) at 1
    return {};
  }
  if (get_upper(res) == get_lower(cur))
  {
    // upper(res) at 2
    if (get_upper_open(res) || get_lower_open(cur))
    {
      return {};
    }
    if (!is_point(cur))
    {
      cur = poly::Interval(get_upper(res));
    }
    return {cur};
  }
  Assert(get_upper(res) > get_lower(cur))
      << "Comparison operator does weird stuff.";
  if (get_upper(res) < get_upper(cur))
  {
    // upper(res) at 3
    if (get_lower(res) < get_lower(cur))
    {
      // lower(res) at 1
      cur.set_upper(get_upper(res), get_upper_open(res));
      return {cur};
    }
    if (get_lower(res) == get_lower(cur))
    {
      // lower(res) at 2
      cur = poly::Interval(get_lower(cur),
                          get_lower_open(cur) || get_lower_open(res),
                          get_upper(res),
                          get_upper_open(res));
      return {cur};
    }
    Assert(get_lower(res) > get_lower(cur))
        << "Comparison operator does weird stuff.";
    // lower(res) at 3
    cur = res;
    return {cur};
  }
  if (get_upper(res) == get_upper(cur))
  {
    // upper(res) at 4
    if (get_lower(res) < get_lower(cur))
    {
      // lower(res) at 1
      if (get_upper_open(res) && !get_upper_open(cur))
      {
        cur.set_upper(get_upper(cur), true);
      }
      return {cur};
    }
    if (get_lower(res) == get_lower(cur))
    {
      // lower(res) at 2
      if (get_lower_open(res) && !get_lower_open(cur))
      {
        cur.set_lower(get_lower(cur), true);
      }
      if (get_upper_open(res) && !get_upper_open(cur))
      {
        cur.set_upper(get_upper(cur), true);
      }
      return {cur};
    }
    Assert(get_lower(res) > get_lower(cur))
        << "Comparison operator does weird stuff.";
    // lower(res) at 3
    cur = poly::Interval(get_lower(res),
                        get_lower_open(res),
                        get_upper(res),
                        get_upper_open(cur) || get_upper_open(res));
    return {cur};
  }

  Assert(get_upper(res) > get_upper(cur))
      << "Comparison operator does weird stuff.";
  // upper(res) at 5

  if (get_lower(res) < get_lower(cur))
  {
    // lower(res) at 1
    return {cur};
  }
  if (get_lower(res) == get_lower(cur))
  {
    // lower(res) at 2
    if (get_lower_open(res) && is_point(cur))
    {
      return {};
    }
    else if (get_lower_open(res) && !get_lower_open(cur))
    {
      cur.set_lower(get_lower(cur), true);
    }
    return {cur};
  }
  Assert(get_lower(res) > get_lower(cur))
      << "Comparison operator does weird stuff.";
  if (get_lower(res) < get_upper(cur))
  {
    // lower(res) at 3
    cur.set_lower(get_lower(res), get_lower_open(res));
    return {cur};
  }
  if (get_lower(res) == get_upper(cur))
  {
    // lower(res) at 4
    if (get_lower_open(res) || get_upper_open(cur))
    {
      return {};
    }
    if (!is_point(cur))
    {
      cur = poly::Interval(get_lower(res));
    }
    return {cur};
  }

  Assert(get_lower(res) > get_upper(cur));
  // lower(res) at 5
  return {};
}
std::vector<poly::Interval> intervalIntersect(const std::vector<poly::Interval>& a, const poly::Interval& b){
  // (a1 \cup a2 \cup ...) \cap b = a1 \cap b \cup a2 \cap b ...
  std::vector<Interval> res;
  for(size_t i=0;i<a.size();i++){
    auto tres = intervalIntersect(a[i], b);
    res.insert(res.end(), tres.begin(), tres.end());
  }
  cleanIntervals(res);
  return res;
}
std::vector<poly::Interval> intervalIntersect(const poly::Interval& a, const std::vector<poly::Interval>& b){
  // a \cap (b1 \cup b2 \cup ...)  = a \cap b1 \cup a \cap b2 ...
  std::vector<Interval> res;
  for(size_t j=0;j<b.size();j++){
    auto tres = intervalIntersect(a, b[j]);
    res.insert(res.end(), tres.begin(), tres.end());
  }
  cleanIntervals(res);
  return res;
}
std::vector<poly::Interval> intervalIntersect(const std::vector<poly::Interval>& a, const std::vector<poly::Interval>& b){
  std::vector<Interval> res;
  for(size_t i=0;i<a.size();i++){
    std::vector<Interval> tres;
    tres.emplace_back(a[i]);
    bool empty = false;
    for(size_t j=0;j<b.size();j++){
      auto ttres = intervalIntersect(tres, b[j]);
      if(ttres.size() == 0){
        empty = true;
        break;
      }
      tres.clear();
      tres.insert(tres.end(), ttres.begin(), ttres.end());
    }
    if(!empty) res.insert(res.end(), tres.begin(), tres.end());
  }
  cleanIntervals(res);
  return res;
}


poly::SignCondition ConditionNot(const poly::SignCondition& sc){
  switch (sc) {
    case poly::SignCondition::LT: return poly::SignCondition::GE; // <   ->  >=
    case poly::SignCondition::LE: return poly::SignCondition::GT; // <=  ->  >
    case poly::SignCondition::EQ: return poly::SignCondition::NE; // =   ->  !=
    case poly::SignCondition::NE: return poly::SignCondition::EQ; // !=  ->  =
    case poly::SignCondition::GT: return poly::SignCondition::LE; // >   ->  <=
    case poly::SignCondition::GE: return poly::SignCondition::LT; // >=  ->  < 
  }
  return poly::SignCondition::EQ;
}

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
