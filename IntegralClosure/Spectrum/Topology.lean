/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import IntegralClosure.Spectrum
public import IntegralClosure.TensorProduct
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Prime-spectrum embeddings and homeomorphisms from powers in the image

For a homomorphism `A →+* B` of commutative semirings, comap induces the topology
on the prime spectrum of `B` if every element of `B` has a positive natural power
in the image. Together with the power-image injectivity criterion, this makes the
original spectrum map a topological embedding. Exponents may vary with the
element.

The proof lifts each basic open along comap, using Mathlib's basic-open basis
and `PrimeSpectrum.basicOpen_pow`. It separates and generalizes the ring-free
embedding component of Mathlib's `PrimeSpectrum.isHomeomorph_comap`, formalized
by Christian Merten and Junyan Xu from the Stacks Project, Tag 0BR8. That theorem
uses the same positive-power image premise over commutative rings, together with
a kernel consisting of nilpotents, to obtain the stronger homeomorphism conclusion.
Here neither a ring structure nor a kernel condition is needed for the inducing
and embedding components. Those criteria alone give no surjectivity or closed-range
conclusion for the spectrum map. The surjective criteria are recovered with exponent one;
localization embeddings need not satisfy the power-image premise.

If a prime `p` vanishes in an algebra and every element has a `p ^ r`-power
in the scalar image for some `r`, the canonical spectrum map remains an embedding
after arbitrary commutative-semiring base change. This follows from the prime-power
image theorem for tensor products and the positive-power criterion below;
it still asserts no closedness of the spectrum image. For commutative rings, if
every element of the original kernel is nilpotent, this map is a homeomorphism.
The homeomorphism is bundled by `IsHomeomorph.homeomorph`, retaining comap along
the coefficient inclusion as its forward map.

More generally, for any homomorphism of commutative semirings whose comap is a
homeomorphism, the inverse point has ideal equal to the radical of the extended
source prime. This inverse description follows from preservation of point closures
and the zero-locus and vanishing-ideal correspondence.

## References

- [Stacks Project, Tag 0BR8](https://stacks.math.columbia.edu/tag/0BR8)
- Mathlib's `PrimeSpectrum.isHomeomorph_comap`, by Christian Merten and Junyan Xu
- Mathlib's `PrimeSpectrum.comap_isInducing_of_surjective`
- Mathlib's `PrimeSpectrum.isEmbedding_comap_of_surjective`
- Mathlib's `PrimeSpectrum.isTopologicalBasis_basic_opens`
- Mathlib's `PrimeSpectrum.basicOpen_pow`
- Mathlib's `PrimeSpectrum.nontrivial_iff_mem_rangeComap`
- Mathlib's `IsHomeomorph.homeomorph` and `isHomeomorph_iff_isEmbedding_surjective`
- Mathlib's `Homeomorph.preimage_closure` and `PrimeSpectrum.closure_singleton`
- Mathlib's `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`
-/

@[expose] public section

universe u v w

namespace PrimeSpectrum

/-- Comap induces the topology on the prime spectrum if every target element
has a positive power in the range of the original semiring homomorphism.
This is the ring-free inducing component of Mathlib's
`PrimeSpectrum.isHomeomorph_comap`, following the Stacks Project, Tag 0BR8. -/
theorem comap_isInducing_of_forall_pow_mem_range
    {A : Type u} {B : Type v} [CommSemiring A] [CommSemiring B]
    (f : A →+* B)
    (hpow : ∀ b : B, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ Set.range f) :
    Topology.IsInducing (PrimeSpectrum.comap f) := by
  refine ⟨le_antisymm (continuous_comap f).le_induced ?_⟩
  rw [(isTopologicalBasis_basic_opens (R := B)).eq_generateFrom]
  apply le_generateFrom
  rintro _ ⟨b, rfl⟩
  -- Normalize the generator application without changing the induced topology.
  change @IsOpen (PrimeSpectrum B)
    (TopologicalSpace.induced (comap f) inferInstance) (basicOpen b : Set (PrimeSpectrum B))
  obtain ⟨n, hn, a, ha⟩ := hpow b
  rw [← basicOpen_pow b n hn, ← ha]
  exact isOpen_induced (f := comap f) isOpen_basicOpen

/-- Comap is a topological embedding if every target element has a positive
power in the range of the original semiring homomorphism. The exponent may
depend on the element; the homomorphism need not be surjective.
This generalizes the embedding component of Mathlib's
`PrimeSpectrum.isHomeomorph_comap` (Stacks Project, Tag 0BR8), without its ring
or nilpotent-kernel hypotheses. -/
theorem isEmbedding_comap_of_forall_pow_mem_range
    {A : Type u} {B : Type v} [CommSemiring A] [CommSemiring B]
    (f : A →+* B)
    (hpow : ∀ b : B, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ Set.range f) :
    Topology.IsEmbedding (PrimeSpectrum.comap f) :=
  ⟨comap_isInducing_of_forall_pow_mem_range f hpow,
    comap_injective_of_forall_pow_mem_range f hpow⟩

/-- The inverse of a spectrum homeomorphism induced by a homomorphism sends a
prime ideal to the radical of its extension. -/
theorem homeomorph_comap_symm_asIdeal
    {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (f : R →+* S)
    (hf : IsHomeomorph (PrimeSpectrum.comap f)) (P : PrimeSpectrum R) :
    ((IsHomeomorph.homeomorph (PrimeSpectrum.comap f) hf).symm P).asIdeal =
      (Ideal.map f P.asIdeal).radical := by
  let e : PrimeSpectrum S ≃ₜ PrimeSpectrum R :=
    IsHomeomorph.homeomorph (PrimeSpectrum.comap f) hf
  have hpre : e ⁻¹' ({P} : Set (PrimeSpectrum R)) = {e.symm P} := by
    ext Q
    change e Q = P ↔ Q = e.symm P
    exact e.eq_symm_apply.symm
  have hz : zeroLocus (Ideal.map f P.asIdeal : Set S) =
      closure ({e.symm P} : Set (PrimeSpectrum S)) := by
    calc
      zeroLocus (Ideal.map f P.asIdeal : Set S) =
          zeroLocus (f '' (P.asIdeal : Set R)) := by
        rw [Ideal.map, zeroLocus_span]
      _ = e ⁻¹' zeroLocus (P.asIdeal : Set R) :=
        (preimage_comap_zeroLocus f _).symm
      _ = e ⁻¹' closure ({P} : Set (PrimeSpectrum R)) := by
        rw [closure_singleton]
      _ = closure (e ⁻¹' ({P} : Set (PrimeSpectrum R))) := e.preimage_closure _
      _ = closure ({e.symm P} : Set (PrimeSpectrum S)) := by rw [hpre]
  change (e.symm P).asIdeal = _
  calc
    (e.symm P).asIdeal =
        vanishingIdeal (closure ({e.symm P} : Set (PrimeSpectrum S))) := by
      rw [vanishingIdeal_closure, vanishingIdeal_singleton]
    _ = vanishingIdeal (zeroLocus (Ideal.map f P.asIdeal : Set S)) :=
      congrArg vanishingIdeal hz.symm
    _ = (Ideal.map f P.asIdeal).radical := vanishingIdeal_zeroLocus_eq_radical _

open scoped TensorProduct

/-- The canonical prime-spectrum map after scalar extension is a topological
embedding if a prime `p` vanishes in the original algebra and each element has
a `p ^ r`-power in the scalar image for some `r`. -/
theorem isEmbedding_comap_algebraMap_tensorProduct_of_forall_pow_pow_mem_range
    {A : Type u} {B : Type v} {C : Type w}
    [CommSemiring A] [CommSemiring B] [CommSemiring C]
    [Algebra A B] [Algebra A C]
    (p : ℕ) (hp : p.Prime) (hB : (p : B) = 0)
    (hpow : ∀ b : B, ∃ r : ℕ, b ^ (p ^ r) ∈ Set.range (algebraMap A B)) :
    Topology.IsEmbedding
      (PrimeSpectrum.comap (algebraMap C (C ⊗[A] B))) := by
  apply isEmbedding_comap_of_forall_pow_mem_range (algebraMap C (C ⊗[A] B))
  intro x
  obtain ⟨s, hs⟩ :=
    Algebra.TensorProduct.exists_pow_pow_mem_range_algebraMap p hp hB hpow x
  exact ⟨p ^ s, pow_pos hp.pos s, hs⟩

/-- If a prime `p` vanishes in an algebra, every element has a `p ^ r`-power
in the scalar image for some `r`, and every element of the kernel is nilpotent,
the canonical prime-spectrum map after any commutative-ring scalar extension
is a homeomorphism.

The associated bundled homeomorphism is
```
IsHomeomorph.homeomorph
  (PrimeSpectrum.comap (algebraMap C (C ⊗[A] B)))
  (isHomeomorph_comap_algebraMap_tensorProduct_of_forall_pow_pow_mem_range
    (A := A) (B := B) (C := C) p hp hB hpow hnil)
```
of type `PrimeSpectrum (C ⊗[A] B) ≃ₜ PrimeSpectrum C`. Its forward map is comap
along the coefficient inclusion. Its inverse prime ideal is described by
`homeomorph_comap_symm_asIdeal`. -/
theorem isHomeomorph_comap_algebraMap_tensorProduct_of_forall_pow_pow_mem_range
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (p : ℕ) (hp : p.Prime) (hB : (p : B) = 0)
    (hpow : ∀ b : B, ∃ r : ℕ, b ^ (p ^ r) ∈ Set.range (algebraMap A B))
    (hnil : ∀ a : A, algebraMap A B a = 0 → IsNilpotent a) :
    IsHomeomorph (PrimeSpectrum.comap (algebraMap C (C ⊗[A] B))) := by
  have hpos : ∀ b : B, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ Set.range (algebraMap A B) := by
    intro b
    obtain ⟨r, hr⟩ := hpow b
    exact ⟨p ^ r, pow_pos hp.pos r, hr⟩
  have hker : RingHom.ker (algebraMap A B) ≤ nilradical A := by
    intro a ha
    exact mem_nilradical.mpr (hnil a (RingHom.mem_ker.mp ha))
  have hOrd := PrimeSpectrum.isHomeomorph_comap (algebraMap A B) hpos hker
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨isEmbedding_comap_algebraMap_tensorProduct_of_forall_pow_pow_mem_range
        (A := A) (B := B) (C := C) p hp hB hpow,
      comap_surjective_algebraMap_tensorProduct (A := A) (B := B) (C := C)
        hOrd.surjective⟩

end PrimeSpectrum
