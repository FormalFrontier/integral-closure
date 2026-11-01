/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import IntegralClosure

/-!
# Surjective specialization of the power-image criterion

The positive-power criterion recovers Mathlib's surjective comap-injectivity
result using exponent one and a preimage. This also checks the root import.
-/

universe u v

private theorem comap_injective_of_surjective
    {A : Type u} {B : Type v} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (hf : Function.Surjective f) :
    Function.Injective (PrimeSpectrum.comap f) := by
  apply PrimeSpectrum.comap_injective_of_forall_pow_mem_range f
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨1, Nat.zero_lt_one, a, (pow_one (f a)).symm⟩
