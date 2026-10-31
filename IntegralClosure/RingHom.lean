/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import IntegralClosure.Polynomial
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

universe u v

namespace RingHom

/-- A ring homomorphism is integral if every target element has a positive power in its range. -/
theorem isIntegral_of_forall_pow_mem_range
    {R : Type u} {S : Type v} [CommRing R] [Ring S]
    (f : R →+* S)
    (hf : ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range f) : f.IsIntegral := by
  intro x
  obtain ⟨n, hn, r, hr⟩ := hf x
  refine ⟨Polynomial.X ^ n - Polynomial.C r,
    Polynomial.monic_X_pow_sub_C r (ne_of_gt hn), ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hr, sub_self]

/-- An element is integral if one of its positive powers is integral. -/
theorem IsIntegralElem.of_pow
    {R : Type u} {S : Type v} [CommRing R] [Ring S]
    {f : R →+* S} {x : S} {n : ℕ} (hn : 0 < n)
    (hx : f.IsIntegralElem (x ^ n)) : f.IsIntegralElem x := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨Polynomial.expand R n p, (Polynomial.monic_expand_iff hn).2 hp, ?_⟩
  rw [Polynomial.eval₂_expand, hpx]

end RingHom
