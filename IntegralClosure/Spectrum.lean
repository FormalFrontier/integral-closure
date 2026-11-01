/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Prime-spectrum injectivity from powers in the image

A homomorphism of commutative semirings induces an injective map on prime spectra
if every target element has a positive natural power in its image. The exponent
may depend on the element. This is a spectrum counterpart to the positive-power
criteria for integrality and finiteness; the proof needs no ring structure or
integrality hypothesis.

The result generalizes Mathlib's `PrimeSpectrum.comap_injective_of_surjective`.
It uses Mathlib's prime power-membership criterion to recover membership from
contraction. Only injectivity of the original spectrum map is asserted, not
surjectivity, a homeomorphism or universal injectivity.

## References

- Mathlib's `PrimeSpectrum.comap_injective_of_surjective`
- Mathlib's `Ideal.IsPrime.pow_mem_iff_mem`
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
  apply Ideal.ext
  intro b
  obtain ⟨n, hn, a, ha⟩ := hpow b
  calc
    b ∈ P.asIdeal ↔ b ^ n ∈ P.asIdeal := (P.isPrime.pow_mem_iff_mem n hn).symm
    _ ↔ b ^ n ∈ Q.asIdeal := by
      have hmem : a ∈ (comap f P).asIdeal ↔ a ∈ (comap f Q).asIdeal := by
        rw [h]
      simpa only [comap_asIdeal, Ideal.mem_comap, ha] using hmem
    _ ↔ b ∈ Q.asIdeal := Q.isPrime.pow_mem_iff_mem n hn

end PrimeSpectrum
