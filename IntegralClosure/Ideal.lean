/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Maps

/-!
# Radical extension and contraction from powers in the image

For a homomorphism from a semiring to a commutative semiring, positive powers of a
target ideal's generators in the image suffice to recover its radical by extension
after contraction. Exponents may depend on the generators, and no finite generation
is required. The source semiring need not be commutative: every radical is in the target.

The global power-image condition makes contraction injective on radical ideals,
without asserting injectivity on all ideals or equality before taking radicals.
The proofs use Mathlib's span, radical and map/comap universal properties, rather
than a ring-theoretic integrality argument.

## References

- Mathlib's `Ideal.map_comap_of_surjective`
- Mathlib's `Ideal.span_le` and `Ideal.radical_le_radical_iff`
-/

@[expose] public section

universe u v

namespace Ideal

/-- Powers of target ideal generators in the image suffice for radical extension after
contraction to recover the radical of their span. The positive exponent may vary
with the generator. -/
theorem radical_map_comap_span_of_forall_pow_mem_range
    {A : Type u} {B : Type v} [Semiring A] [CommSemiring B]
    (f : A →+* B) (s : Set B)
    (hpow : ∀ b ∈ s, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ Set.range f) :
    (Ideal.map f (Ideal.comap f (Ideal.span s))).radical = (Ideal.span s).radical := by
  refine le_antisymm (radical_mono map_comap_le) ?_
  rw [radical_le_radical_iff, span_le]
  intro b hb
  obtain ⟨n, hn, a, ha⟩ := hpow b hb
  refine mem_radical_iff.mpr ⟨n, ?_⟩
  rw [← ha]
  apply mem_map_of_mem f
  rw [mem_comap, ha]
  exact (Ideal.span s).pow_mem_of_mem (subset_span hb) n hn

/-- Radical extension after contraction recovers the radical of an ideal if each
of its elements has a positive power in the image. No condition outside the ideal
is required. -/
theorem radical_map_comap_of_forall_mem_exists_pow_mem_range
    {A : Type u} {B : Type v} [Semiring A] [CommSemiring B]
    (f : A →+* B) (J : Ideal B)
    (hpow : ∀ b ∈ J, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ Set.range f) :
    (Ideal.map f (Ideal.comap f J)).radical = J.radical := by
  simpa only [span_eq] using
    radical_map_comap_span_of_forall_pow_mem_range f (J : Set B) hpow

/-- If every target element has a positive power in the image, contraction is
injective on radical ideals. The source need not be commutative. -/
theorem comap_injOn_isRadical_of_forall_pow_mem_range
    {A : Type u} {B : Type v} [Semiring A] [CommSemiring B]
    (f : A →+* B) (hpow : ∀ b : B, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ Set.range f) :
    Set.InjOn (Ideal.comap f) {J : Ideal B | J.IsRadical} := by
  intro I hI J hJ hIJ
  calc
    I = I.radical := (radical_eq_iff.mpr hI).symm
    _ = (Ideal.map f (Ideal.comap f I)).radical :=
      (radical_map_comap_of_forall_mem_exists_pow_mem_range f I (fun b _ ↦ hpow b)).symm
    _ = (Ideal.map f (Ideal.comap f J)).radical := by rw [hIJ]
    _ = J.radical :=
      radical_map_comap_of_forall_mem_exists_pow_mem_range f J (fun b _ ↦ hpow b)
    _ = J := radical_eq_iff.mpr hJ

end Ideal
