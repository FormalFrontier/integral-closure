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

end Polynomial
