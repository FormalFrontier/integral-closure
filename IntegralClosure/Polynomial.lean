/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Polynomial relations under raw evaluation

The coefficient images need not be central in the target semiring.
-/

open scoped BigOperators

@[expose] public section

universe u v

/-- Clear inverse powers in a reflected weighted sum over a finite range.
No commutativity of multiplication is required. -/
theorem Finset.sum_range_reflect_mul_pow
    {S : Type u} [Semiring S] (c : ℕ → S) (x : S) [Invertible x] (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), c (N - k) * (⅟x) ^ k) * x ^ N =
      ∑ k ∈ Finset.range (N + 1), c k * x ^ k := by
  have hcancel (k : ℕ) : (⅟x) ^ k * x ^ k = (1 : S) := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        (⅟x) ^ (k + 1) * x ^ (k + 1) =
            (⅟x) ^ k * ((⅟x * x) * x ^ k) := by
          rw [pow_succ, pow_succ']
          simp only [mul_assoc]
        _ = 1 := by rw [invOf_mul_self, one_mul, ih]
  calc
    (∑ k ∈ Finset.range (N + 1), c (N - k) * (⅟x) ^ k) * x ^ N =
        ∑ k ∈ Finset.range (N + 1), c (N - k) * x ^ (N - k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hp : x ^ N = x ^ k * x ^ (N - k) := by
        rw [← pow_add, Nat.add_sub_of_le hkN]
      rw [hp, mul_assoc,
        ← mul_assoc ((⅟x) ^ k) (x ^ k) (x ^ (N - k)),
        hcancel k, one_mul]
    _ = ∑ k ∈ Finset.range (N + 1), c k * x ^ k := by
      simpa only [Nat.add_sub_cancel] using
        (Finset.sum_range_reflect (fun k => c k * x ^ k) (N + 1))

namespace Polynomial

/-- Evaluation commutes with substitution by a power of X in a noncommutative target. -/
theorem eval₂_comp_X_pow
    {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →+* S) (x : S) (n : ℕ) (p : R[X]) :
    eval₂ f x (p.comp (X ^ n)) = eval₂ f (x ^ n) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.add_comp, Polynomial.eval₂_add, hp, hq]
  | monomial i a =>
      simp only [Polynomial.comp, Polynomial.eval₂_monomial, ← pow_mul,
        Polynomial.C_mul_X_pow_eq_monomial]

/-- Evaluation commutes with power substitution without centrality of the coefficient images. -/
@[simp] theorem eval₂_expand
    {R : Type u} {S : Type v} [CommSemiring R] [Semiring S]
    (f : R →+* S) (x : S) (n : ℕ) (p : R[X]) :
    eval₂ f x (expand R n p) = eval₂ f (x ^ n) p := by
  rw [expand_eq_comp_X_pow, eval₂_comp_X_pow]

/-- Every left multiple of a polynomial vanishing under evaluation also vanishes. -/
theorem eval₂_mul_eq_zero_of_right'
    {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →+* S) (x : S) (p : R[X]) {q : R[X]}
    (hq : q.eval₂ f x = 0) : (p * q).eval₂ f x = 0 := by
  induction p using Polynomial.induction_on with
  | C a =>
      simpa only [eval₂_eq_eval_map, Polynomial.map_mul, map_C,
        eval_C_mul, mul_zero] using congrArg (fun y => f a * y) hq
  | add p₁ p₂ h₁ h₂ =>
      rw [add_mul, eval₂_add, h₁, h₂, add_zero]
  | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, mul_assoc, X_mul, ← mul_assoc,
        eval₂_mul_X, ih, zero_mul]

section

variable {R : Type u} {S : Type v} [Semiring R] [Semiring S]

/-- Reciprocal evaluation, without commutativity of the target semiring. -/
theorem eval₂_reflect_mul_pow' (i : R →+* S) (x : S) [Invertible x]
    (N : ℕ) (p : R[X]) (hp : p.natDegree ≤ N) :
    (reflect N p).eval₂ i (⅟x) * x ^ N = p.eval₂ i x := by
  classical
  have hreflect : (reflect N p).natDegree ≤ N := by
    simpa only [max_eq_left hp] using
      (natDegree_reflect_le (N := N) (p := p))
  calc
    (reflect N p).eval₂ i (⅟x) * x ^ N =
        (∑ k ∈ Finset.range (N + 1),
          i (p.coeff (N - k)) * (⅟x) ^ k) * x ^ N := by
      congr 1
      rw [eval₂_eq_sum,
        sum_over_range' (reflect N p) (f := fun k a => i a * (⅟x) ^ k)
          (fun _ => by simp) (N + 1) (Nat.lt_succ_of_le hreflect)]
      apply Finset.sum_congr rfl
      intro k hk
      rw [coeff_reflect, revAt_le (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    _ = ∑ k ∈ Finset.range (N + 1), i (p.coeff k) * x ^ k :=
      Finset.sum_range_reflect_mul_pow (fun k => i (p.coeff k)) x N
    _ = p.eval₂ i x := by
      rw [eval₂_eq_sum,
        sum_over_range' p (f := fun k a => i a * x ^ k)
          (fun _ => by simp) (N + 1) (Nat.lt_succ_of_le hp)]

end

/-- A polynomial relation at a unit gives a monic relation at its inverse if the
leading coefficient of the reversed polynomial is a unit in the coefficient semiring. -/
theorem exists_monic_eval₂_units_inv_eq_zero_of_isUnit_reverse_leadingCoeff
    {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →+* S) (a : Sˣ) {p : R[X]}
    (hc : IsUnit p.reverse.leadingCoeff) (ha : p.eval₂ f (a : S) = 0) :
    ∃ q : R[X], q.Monic ∧ q.eval₂ f (↑(a⁻¹) : S) = 0 := by
  rcases hc with ⟨c, hc⟩
  let : Invertible (a : S) :=
    ⟨↑(a⁻¹), a.inv_val, a.val_inv⟩
  have hr : p.reverse.eval₂ f (↑(a⁻¹) : S) = 0 := by
    have h := eval₂_reflect_mul_pow' f (a : S) p.natDegree p le_rfl
    change p.reverse.eval₂ f (↑(a⁻¹) : S) * (a : S) ^ p.natDegree =
      p.eval₂ f (a : S) at h
    rw [ha] at h
    have hi : (a : S) ^ p.natDegree *
        (↑((a ^ p.natDegree)⁻¹) : S) = 1 :=
      (a ^ p.natDegree).val_inv
    have h' := congrArg
      (fun z : S => z * (↑((a ^ p.natDegree)⁻¹) : S)) h
    simpa only [mul_assoc, hi, mul_one, zero_mul] using h'
  refine ⟨C (↑(c⁻¹) : R) * p.reverse, ?_, ?_⟩
  · apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [← hc]
    exact c.inv_val
  · exact eval₂_mul_eq_zero_of_right' f _ _ hr

/-- A nonzero polynomial relation at a unit over a division semiring yields a monic relation
at its inverse. Coefficient images need not be central in the target semiring. -/
theorem exists_monic_eval₂_units_inv_eq_zero
    {R : Type u} {S : Type v} [DivisionSemiring R] [Semiring S]
    (f : R →+* S) (a : Sˣ) {p : R[X]} (hp : p ≠ 0)
    (ha : p.eval₂ f (a : S) = 0) :
    ∃ q : R[X], q.Monic ∧ q.eval₂ f (↑(a⁻¹) : S) = 0 := by
  apply exists_monic_eval₂_units_inv_eq_zero_of_isUnit_reverse_leadingCoeff f a (p := p)
  · apply isUnit_iff_ne_zero.mpr
    apply leadingCoeff_ne_zero.mpr
    exact fun h => hp (reverse_eq_zero.mp h)
  · exact ha

end Polynomial
