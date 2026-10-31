/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Expand

/-!
# Evaluation after power substitution

The coefficient images need not be central in the target semiring.
-/

@[expose] public section

universe u v

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

end Polynomial
