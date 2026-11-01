/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import IntegralClosure.RingHom
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Finiteness over power-containing subalgebras

A finite-type commutative algebra is finite over any subalgebra containing a
positive power of each of its elements. The exponent may depend on the element.
The scalar action on the ambient algebra is the canonical inclusion action.

The proof uses the positive-power range criterion for integrality and Mathlib's
finite-type restriction-of-scalars and integral-finiteness theorems.

## References

- `RingHom.isIntegral_of_forall_pow_mem_range`
- Mathlib's `Algebra.FiniteType.of_restrictScalars_finiteType` and
  `Algebra.IsIntegral.finite`
-/

@[expose] public section

universe u v

/-- A finite-type commutative algebra is finite over a subalgebra containing a
positive power of every element. Neither finite type of the subalgebra over the
original base nor a common exponent is required. -/
theorem Subalgebra.finite_of_forall_exists_pow_mem
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A]
    (C : Subalgebra R A)
    (hpow : ∀ a : A, ∃ n : ℕ, 0 < n ∧ a ^ n ∈ C) : Module.Finite C A := by
  have hi : (algebraMap C A).IsIntegral :=
    RingHom.isIntegral_of_forall_pow_mem_range _ fun a ↦ by
      obtain ⟨n, hn, ha⟩ := hpow a
      exact ⟨n, hn, ⟨⟨a ^ n, ha⟩, rfl⟩⟩
  let : Algebra.IsIntegral C A := algebraMap_isIntegral_iff.mp hi
  let : Algebra.FiniteType C A :=
    Algebra.FiniteType.of_restrictScalars_finiteType R C A
  exact Algebra.IsIntegral.finite
