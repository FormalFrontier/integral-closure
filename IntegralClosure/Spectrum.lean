/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import IntegralClosure.Ideal

/-!
# Prime-spectrum injectivity from powers in the image

A homomorphism of commutative semirings induces an injective map on prime spectra
if every target element has a positive natural power in its image. The exponent
may depend on the element. This is a spectrum counterpart to the positive-power
criteria for integrality and finiteness; the proof needs no ring structure or
integrality hypothesis.

The result generalizes Mathlib's `PrimeSpectrum.comap_injective_of_surjective`.
It follows from contraction injectivity on radical ideals, since prime ideals are
radical. Only injectivity of the original spectrum map is asserted, not
surjectivity, a homeomorphism or universal injectivity.

## References

- Mathlib's `PrimeSpectrum.comap_injective_of_surjective`
- `Ideal.comap_injOn_isRadical_of_forall_pow_mem_range`
- Mathlib's `Ideal.IsPrime.isRadical`
-/

@[expose] public section

universe u v

namespace PrimeSpectrum

/-- A homomorphism of commutative semirings induces an injective map on prime spectra
if every target element has a positive power in its range. The exponent may depend
on the element; surjectivity of the homomorphism is not required.

This generalizes Mathlib's `PrimeSpectrum.comap_injective_of_surjective`. -/
theorem comap_injective_of_forall_pow_mem_range
    {A : Type u} {B : Type v} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (hpow : ∀ b : B, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ Set.range f) :
    Function.Injective (comap f) := by
  intro P Q h
  apply PrimeSpectrum.ext
  exact Ideal.comap_injOn_isRadical_of_forall_pow_mem_range f hpow
    P.isPrime.isRadical Q.isPrime.isRadical
    (by simpa only [comap_asIdeal] using congrArg PrimeSpectrum.asIdeal h)

end PrimeSpectrum
