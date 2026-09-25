/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral closure descends along linear retractions

This file proves that an injective algebra map into an integrally closed domain
descends integral closedness when it admits a linear retraction. The proof does
not require the map to be integral or the retraction to preserve multiplication.
Commutative rings A and B may inhabit independent universes. Domain and
integral-closedness assumptions are on B; the domain structure on A is obtained
from the injective algebra map inside the theorem.
-/

set_option warningAsError true

noncomputable section

public section

universe u v

namespace IsIntegrallyClosed

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- An injective algebra map into an integrally closed domain descends integral
closedness when it has an A-linear left inverse `r`. Injectivity is an explicit
argument. No ring-homomorphism property of `r` or integrality of the map is
assumed.

The proof transfers an integral fraction into the fraction ring of B, where it
equals some `b : B`. After writing the original fraction as `a/s`, its equality
in the fraction ring clears to `algebraMap A B s * b = algebraMap A B a`.
A-linearity of `r` then gives `s * r b = a`, proving that `r b` represents the
fraction over A. Nonzero denominators and injectivity justify the cancellations;
`r` is never used as a multiplicative map. -/
theorem of_linearRetract [IsDomain B] [IsIntegrallyClosed B]
    (hinj : Function.Injective (algebraMap A B))
    (r : B →ₗ[A] A) (hr : ∀ a, r (algebraMap A B a) = a) :
    IsIntegrallyClosed A := by
  let _ : IsDomain A := hinj.isDomain (algebraMap A B)
  let _ : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  let _ : Algebra (FractionRing A) (FractionRing B) :=
    FractionRing.liftAlgebra A (FractionRing B)
  let _ : IsScalarTower A (FractionRing A) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  have hx' : IsIntegral B (algebraMap (FractionRing A) (FractionRing B) x) :=
    (hx.map (IsScalarTower.toAlgHom A (FractionRing A) (FractionRing B))).tower_top
  obtain ⟨b, hb⟩ :=
    (isIntegrallyClosed_iff (FractionRing B)).mp (inferInstance : IsIntegrallyClosed B) hx'
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective A x
  refine ⟨r b, ?_⟩
  have hcrossB : algebraMap A B s * b = algebraMap A B a :=
    (IsFractionRing.injective B (FractionRing B)) (by
      rw [map_mul, hb]
      rw [map_div₀,
        ← IsScalarTower.algebraMap_apply A B (FractionRing B) s,
        ← IsScalarTower.algebraMap_apply A B (FractionRing B) a,
        ← IsScalarTower.algebraMap_apply A (FractionRing A) (FractionRing B) a,
        ← IsScalarTower.algebraMap_apply A (FractionRing A) (FractionRing B) s]
      have hsL : algebraMap A (FractionRing B) s ≠ 0 := by
        simpa using (FaithfulSMul.algebraMap_injective A (FractionRing B)).ne
          (nonZeroDivisors.ne_zero hs)
      exact mul_div_cancel₀ _ hsL)
  have hretract : s * r b = a := by
    change s • r b = a
    rw [← r.map_smul, Algebra.smul_def, hcrossB, hr]
  have hsK : algebraMap A (FractionRing A) s ≠ 0 := by
    simpa using (IsFractionRing.injective A (FractionRing A)).ne
      (nonZeroDivisors.ne_zero hs)
  apply (eq_div_iff hsK).2
  simpa [← map_mul, mul_comm] using congrArg (algebraMap A (FractionRing A)) hretract

end IsIntegrallyClosed

end
