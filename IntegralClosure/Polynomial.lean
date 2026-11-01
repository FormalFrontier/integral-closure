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

/-- Reversing a polynomial and inverting the evaluation point preserves vanishing,
without centrality of the coefficient images. -/
@[simp] theorem eval₂_reverse_eq_zero_iff' (f : R →+* S) (x : S) [Invertible x]
    (p : R[X]) : p.reverse.eval₂ f (⅟x) = 0 ↔ p.eval₂ f x = 0 := by
  have h := eval₂_reflect_mul_pow' f x p.natDegree p le_rfl
  change p.reverse.eval₂ f (⅟x) * x ^ p.natDegree = p.eval₂ f x at h
  rw [← h, (isUnit_of_invertible (x ^ p.natDegree)).mul_left_eq_zero]

end

private theorem eval₂_reverse_eq_zero_iff'_eq
    {R : Type u} {S : Type v} [Semiring R] [CommSemiring S]
    (f : R →+* S) (x : S) [Invertible x] (p : R[X]) :
    eval₂_reverse_eq_zero_iff' f x p = eval₂_reverse_eq_zero_iff f x p :=
  Subsingleton.elim _ _

/-- A polynomial relation at a unit gives a monic relation at its inverse if the
leading coefficient of the reversed polynomial is a unit in the coefficient semiring. -/
theorem exists_monic_eval₂_units_inv_eq_zero_of_isUnit_reverse_leadingCoeff
    {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →+* S) (a : Sˣ) {p : R[X]}
    (hc : IsUnit p.reverse.leadingCoeff) (ha : p.eval₂ f (a : S) = 0) :
    ∃ q : R[X], q.Monic ∧ q.eval₂ f (↑(a⁻¹) : S) = 0 := by
  rcases hc with ⟨c, hc⟩
  have hr : p.reverse.eval₂ f (↑(a⁻¹) : S) = 0 := by
    simpa only [invOf_units] using (eval₂_reverse_eq_zero_iff' f (a : S) p).mpr ha
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

/-- Monic relations at a unit and its inverse yield a monic relation at the unit
whose constant coefficient is one in the coefficient semiring. -/
theorem exists_monic_coeff_zero_eq_one_eval₂_units_eq_zero
    {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →+* S) (a : Sˣ) {p q : R[X]}
    (hp : p.Monic) (ha : p.eval₂ f (a : S) = 0)
    (hq : q.Monic) (hai : q.eval₂ f (↑(a⁻¹) : S) = 0) :
    ∃ r : R[X], r.Monic ∧ r.coeff 0 = 1 ∧ r.eval₂ f (a : S) = 0 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · let _ := hR
    exact ⟨0, monic_of_subsingleton _, Subsingleton.elim _ _, eval₂_zero f _⟩
  · let _ := hR
    let : Invertible (↑(a⁻¹) : S) := (a⁻¹).invertible
    have hrev : q.reverse.eval₂ f (a : S) = 0 := by
      simpa only [invOf_units, inv_inv] using
        (eval₂_reverse_eq_zero_iff' f (↑(a⁻¹) : S) q).2 hai
    have hmul (n : ℕ) : (p * X ^ n).eval₂ f (a : S) = 0 := by
      induction n with
      | zero => simpa only [pow_zero, mul_one] using ha
      | succ n ih =>
          rw [pow_succ, ← mul_assoc, eval₂_mul_X, ih, zero_mul]
    let k := q.reverse.natDegree + 1
    refine ⟨p * X ^ k + q.reverse, ?_, ?_, ?_⟩
    · apply (hp.mul (monic_X_pow k)).add_of_left
      apply degree_lt_degree
      rw [natDegree_mul_X_pow k hp.ne_zero]
      exact (Nat.lt_succ_self _).trans_le (Nat.le_add_left _ _)
    · rw [coeff_add, mul_coeff_zero, coeff_X_pow, coeff_zero_reverse, hq]
      simp [k]
    · rw [eval₂_add, hmul k, hrev, add_zero]

/-- A unit and its inverse both admit monic polynomial relations if and only if the
unit admits a monic relation with a unit constant coefficient in the coefficient semiring. -/
theorem exists_monic_eval₂_units_eq_zero_and_inv_iff
    {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →+* S) (a : Sˣ) :
    ((∃ p : R[X], p.Monic ∧ p.eval₂ f (a : S) = 0) ∧
      (∃ q : R[X], q.Monic ∧ q.eval₂ f (↑(a⁻¹) : S) = 0)) ↔
    ∃ p : R[X], p.Monic ∧ IsUnit (p.coeff 0) ∧ p.eval₂ f (a : S) = 0 := by
  constructor
  · rintro ⟨⟨p, hp, ha⟩, ⟨q, hq, hai⟩⟩
    obtain ⟨r, hr, hc, har⟩ :=
      exists_monic_coeff_zero_eq_one_eval₂_units_eq_zero f a hp ha hq hai
    refine ⟨r, hr, ?_, har⟩
    rw [hc]
    exact isUnit_one
  · rintro ⟨p, hp, hc, ha⟩
    have hreverse : IsUnit p.reverse.leadingCoeff := by
      rcases subsingleton_or_nontrivial R with hR | hR
      · exact isUnit_of_subsingleton _
      · rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero hc.ne_zero]
        exact hc
    exact ⟨⟨p, hp, ha⟩,
      exists_monic_eval₂_units_inv_eq_zero_of_isUnit_reverse_leadingCoeff f a hreverse ha⟩

end Polynomial
