/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import IntegralClosure.RingHom
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Radical extension, contraction and ideal correspondence

For a homomorphism from a semiring to a commutative semiring, positive powers of a
target ideal's generators in the image suffice to recover its radical by extension
after contraction. Exponents may depend on the generators, and no finite generation
is required. In this target-side reconstruction the source semiring need not be
commutative, since all radicals are taken in the target.

The global power-image condition makes contraction injective on radical ideals,
without asserting injectivity on all ideals or equality before taking radicals.
The target-side reconstruction proofs use Mathlib's span, radical and map/comap
universal properties, rather than a ring-theoretic integrality argument.

For a homomorphism between commutative rings, integrality gives the source-side
formula: contraction of the radical of an extended ideal is the radical of its join
with the kernel. Under the global positive-power condition, contraction is an order
isomorphism from radical ideals of the target to radical ideals of the source
containing the kernel. Its inverse is extension followed by radical.

## References

- Mathlib's `Ideal.map_comap_of_surjective`
- Mathlib's `Ideal.span_le` and `Ideal.radical_le_radical_iff`
- Mathlib's `Ideal.exists_ideal_over_prime_of_isIntegral` and `Ideal.radical_eq_sInf`
- Mathlib's `Ideal.relIsoOfSurjective` and `Ideal.map_radical_of_surjective`
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

/-- For an integral homomorphism of commutative rings, contraction of the radical
of an extended ideal is the radical of the join of that ideal with the kernel. -/
theorem comap_radical_map_eq_radical_sup_ker_of_isIntegral
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.IsIntegral) (I : Ideal A) :
    Ideal.comap f (Ideal.map f I).radical = (I ⊔ RingHom.ker f).radical := by
  let : Algebra A B := f.toAlgebra
  let : Algebra.IsIntegral A B := algebraMap_isIntegral_iff.mp hf
  refine le_antisymm ?_ ?_
  · rw [radical_eq_sInf (I ⊔ RingHom.ker f)]
    refine le_sInf fun P hP => ?_
    let : P.IsPrime := hP.2
    have hker : RingHom.ker f ≤ P := le_sup_right.trans hP.1
    obtain ⟨Q, _, hQ, hQP⟩ :=
      exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal B) hker
    have hIP : I ≤ Q.under A := by
      rw [hQP]
      exact le_sup_left.trans hP.1
    have hIQ : Ideal.map f I ≤ Q := map_le_iff_le_comap.mpr hIP
    calc
      Ideal.comap f (Ideal.map f I).radical ≤ Ideal.comap f Q :=
        comap_mono (hQ.radical_le_iff.mpr hIQ)
      _ = P := hQP
  · rw [comap_radical]
    exact radical_mono (sup_le le_comap_map (ker_le_comap f))

/-- If every target element has a positive power in the image of a homomorphism
of commutative rings, contraction is an order isomorphism from radical ideals of
the target to radical ideals of the source containing the kernel. The inverse
sends a source ideal to the radical of its extension. Exponents may vary with the
target element. -/
def radicalComapOrderIsoOfForallPowMemRange
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hpow : ∀ b : B, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ Set.range f) :
    {J : Ideal B // J.IsRadical} ≃o
      {I : Ideal A // I.IsRadical ∧ RingHom.ker f ≤ I} where
  toFun := fun J => ⟨Ideal.comap f J.val, by
    exact ⟨Ideal.IsRadical.comap f J.property, Ideal.ker_le_comap f⟩⟩
  invFun := fun I => ⟨(Ideal.map f I.val).radical, by
    exact Ideal.radical_isRadical _⟩
  left_inv := by
    intro J
    apply Subtype.ext
    change (Ideal.map f (Ideal.comap f J.val)).radical = J.val
    rw [radical_map_comap_of_forall_mem_exists_pow_mem_range f J.val
      (fun b _ => hpow b), J.property.radical]
  right_inv := by
    intro I
    apply Subtype.ext
    change Ideal.comap f (Ideal.map f I.val).radical = I.val
    rw [comap_radical_map_eq_radical_sup_ker_of_isIntegral f
      (RingHom.isIntegral_of_forall_pow_mem_range f hpow) I.val,
      sup_eq_left.mpr I.property.2, I.property.1.radical]
  map_rel_iff' := by
    intro J K
    change Ideal.comap f J.val ≤ Ideal.comap f K.val ↔ J.val ≤ K.val
    constructor
    · intro h
      have hrad := radical_mono (Ideal.map_mono (f := f) h)
      rw [radical_map_comap_of_forall_mem_exists_pow_mem_range f J.val
          (fun b _ => hpow b),
        radical_map_comap_of_forall_mem_exists_pow_mem_range f K.val
          (fun b _ => hpow b),
        J.property.radical, K.property.radical] at hrad
      exact hrad
    · exact Ideal.comap_mono

/-- The radical-ideal order isomorphism acts on underlying ideals by contraction
along the given homomorphism. -/
@[simp]
theorem radicalComapOrderIsoOfForallPowMemRange_apply
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hpow : ∀ b : B, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ Set.range f)
    (J : {J : Ideal B // J.IsRadical}) :
    (radicalComapOrderIsoOfForallPowMemRange f hpow J).val = Ideal.comap f J.val := by
  rfl

/-- The inverse radical-ideal order isomorphism acts on underlying ideals by
extension followed by radical. -/
@[simp]
theorem radicalComapOrderIsoOfForallPowMemRange_symm_apply
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hpow : ∀ b : B, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ Set.range f)
    (I : {I : Ideal A // I.IsRadical ∧ RingHom.ker f ≤ I}) :
    ((radicalComapOrderIsoOfForallPowMemRange f hpow).symm I).val =
      (Ideal.map f I.val).radical := by
  rfl

/-- For a surjective homomorphism, the inverse radical-ideal order isomorphism
acts by extension without taking a further radical, agreeing on underlying ideals
with the inverse of `Ideal.relIsoOfSurjective`. -/
theorem radicalComapOrderIsoOfForallPowMemRange_symm_apply_of_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hpow : ∀ b : B, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ Set.range f)
    (I : {I : Ideal A // I.IsRadical ∧ RingHom.ker f ≤ I})
    (hfSurj : Function.Surjective f) :
    ((radicalComapOrderIsoOfForallPowMemRange f hpow).symm I).val =
      Ideal.map f I.val := by
  rw [radicalComapOrderIsoOfForallPowMemRange_symm_apply,
    ← Ideal.map_radical_of_surjective hfSurj I.property.2, I.property.1.radical]

end Ideal
