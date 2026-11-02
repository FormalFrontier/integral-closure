/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import IntegralClosure.Ideal

/-!
# Prime-spectrum injectivity and surjectivity after scalar extension

A homomorphism of commutative semirings induces an injective map on prime spectra
if every target element has a positive natural power in its image. The exponent
may depend on the element. This is a spectrum counterpart to the positive-power
criteria for integrality and finiteness; the proof needs no ring structure or
integrality hypothesis.

The injectivity result generalizes Mathlib's
`PrimeSpectrum.comap_injective_of_surjective`. It follows from contraction
injectivity on radical ideals, since prime ideals are radical. This criterion
alone does not assert surjectivity, a homeomorphism or universal injectivity.

For commutative rings, surjectivity on prime spectra is preserved by arbitrary
scalar extension. The resulting map is comap along the canonical coefficient
inclusion into the tensor product. This follows from Mathlib's characterization
of the spectrum image by nontrivial residue-field fibers and scalar extension
between residue fields.

## References

- Mathlib's `PrimeSpectrum.comap_injective_of_surjective`
- `Ideal.comap_injOn_isRadical_of_forall_pow_mem_range`
- Mathlib's `Ideal.IsPrime.isRadical`
- Mathlib's `PrimeSpectrum.nontrivial_iff_mem_rangeComap`
-/

@[expose] public section

universe u v w

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

open scoped TensorProduct

/-- Surjectivity of the prime-spectrum map of an algebra is preserved by arbitrary
commutative-ring scalar extension, along the canonical coefficient inclusion. -/
theorem comap_surjective_algebraMap_tensorProduct
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (h : Function.Surjective (PrimeSpectrum.comap (algebraMap A B))) :
    Function.Surjective
      (PrimeSpectrum.comap (algebraMap C (C ⊗[A] B))) := by
  -- First keep the scalar-extension argument independent of the construction of the fields.
  have extendFiber : ∀ (K : Type u) (L : Type w)
      [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra C L]
      [IsScalarTower A C L] [Algebra K L] [IsScalarTower A K L],
      Nontrivial (K ⊗[A] B) → Nontrivial (L ⊗[C] (C ⊗[A] B)) := by
    intro K L _ _ _ _ _ _ _ _ hN
    let N := K ⊗[A] B
    let : Nontrivial N := hN
    let : Module.Free K N := Module.Free.of_divisionRing K N
    let : Module.Flat K N := Module.Flat.of_free
    let ι : N →ₐ[K] L ⊗[K] N := Algebra.TensorProduct.includeRight
    have hι : Function.Injective ι :=
      Algebra.TensorProduct.includeRight_injective (R := K) (A := L) (B := N)
        (RingHom.injective (algebraMap K L))
    let : Nontrivial (L ⊗[K] N) :=
      ⟨⟨ι 0, ι 1, fun h01 => zero_ne_one (hι h01)⟩⟩
    -- The two cancellations have different algebra bases, so use their ring equivalences.
    let e : L ⊗[K] N ≃+* L ⊗[C] (C ⊗[A] B) :=
      (Algebra.TensorProduct.cancelBaseChange A K K L B).toRingEquiv.trans
        (Algebra.TensorProduct.cancelBaseChange A C C L B).symm.toRingEquiv
    exact e.symm.toEquiv.nontrivial
  -- Pass the local algebra and its compatibility data together before specializing to primes.
  have residueFiber : ∀ (U : Type u) (V : Type w)
      [CommRing U] [CommRing V] [IsLocalRing U] [IsLocalRing V]
      [Algebra A U] [Algebra A V] [Algebra C V] [IsScalarTower A C V]
      [Algebra U V] [IsScalarTower A U V] [IsLocalHom (algebraMap U V)],
      Nontrivial (IsLocalRing.ResidueField U ⊗[A] B) →
        Nontrivial (IsLocalRing.ResidueField V ⊗[C] (C ⊗[A] B)) := by
    intro U V _ _ _ _ _ _ _ _ _ _ _ hN
    exact @extendFiber (IsLocalRing.ResidueField U) (IsLocalRing.ResidueField V)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (inferInstance : Algebra (IsLocalRing.ResidueField U) (IsLocalRing.ResidueField V))
      inferInstance hN
  intro P
  let r := PrimeSpectrum.comap (algebraMap A C) P
  have hN : Nontrivial (r.asIdeal.ResidueField ⊗[A] B) :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap (S := B) r).mpr (h r)
  let U := Localization.AtPrime r.asIdeal
  let V := Localization.AtPrime P.asIdeal
  let aUV : Algebra U V := Localization.AtPrime.algebraOfLiesOver r.asIdeal P.asIdeal
  let tUV : @IsScalarTower A U V inferInstance aUV.toSMul inferInstance := inferInstance
  let hUV : IsLocalHom aUV.algebraMap :=
    Localization.isLocalHom_localRingHom r.asIdeal P.asIdeal (algebraMap A C) rfl
  exact (PrimeSpectrum.nontrivial_iff_mem_rangeComap (S := C ⊗[A] B) P).mp
    (@residueFiber U V inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance aUV tUV hUV hN)

end PrimeSpectrum
