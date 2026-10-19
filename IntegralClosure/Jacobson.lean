/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Jacobson.Ideal

import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Jacobson ideals under integral homomorphisms

For an integral homomorphism of commutative rings, contraction commutes with the
Jacobson radical of every ideal. Consequently, extension sends the Jacobson
radical of an ideal into the Jacobson radical of its extension, and preserves
containment in the Jacobson radical of the zero ideal.

Integrality ensures that maximal ideals contract to maximal ideals and supplies
lying over primes containing the kernel. No injectivity, surjectivity, or
nontriviality assumption is needed.
The surjective case also has a formula over possibly noncommutative rings in
Mathlib; that broader ambient setting is distinct from the integral case here.

## References

The Jacobson-ideal formalization and `Ideal.comap_jacobson_of_surjective` are in
Mathlib's `Mathlib.RingTheory.Jacobson.Ideal`, by Kenny Lau, Devon Tuma, and
Wojciech Nawrocki. The integral maximal-ideal contraction and going-up
formalizations are in `Mathlib.RingTheory.Ideal.GoingUp`, by Anne Baanen and
Yongle Hu; see `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`.
-/

public section

universe u v

namespace Ideal

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Contraction along an integral homomorphism commutes with the Jacobson radical
of every ideal. This generalizes Mathlib's
`Ideal.comap_jacobson_of_surjective` in the commutative-ring setting. -/
theorem comap_jacobson_of_isIntegral (f : R →+* S) (hf : f.IsIntegral)
    (J : Ideal S) : J.jacobson.comap f = (J.comap f).jacobson := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.IsIntegral R S := (algebraMap_isIntegral_iff).mp (by
    simpa only [RingHom.algebraMap_toAlgebra] using hf)
  have hmax :
      comap f '' {M : Ideal S | J ≤ M ∧ M.IsMaximal} =
        {m : Ideal R | J.comap f ≤ m ∧ m.IsMaximal} := by
    ext m
    constructor
    · rintro ⟨M, ⟨hJM, hM⟩, rfl⟩
      let : M.IsMaximal := hM
      exact ⟨comap_mono hJM,
        isMaximal_comap_of_isIntegral_of_isMaximal f hf M⟩
    · rintro ⟨hJm, hm⟩
      let : m.IsMaximal := hm
      obtain ⟨M, hJM, hM, hMm⟩ :=
        exists_ideal_over_prime_of_isIntegral m J (by
          simpa only [under_def, RingHom.algebraMap_toAlgebra] using hJm)
      let : M.IsPrime := hM
      have hcomap : M.comap f = m := by
        simpa only [under_def, RingHom.algebraMap_toAlgebra] using hMm
      have hMmax : M.IsMaximal :=
        isMaximal_of_isIntegral_of_isMaximal_comap f hf M (hcomap.symm ▸ hm)
      exact ⟨M, ⟨hJM, hMmax⟩, hcomap⟩
  have hidentity : (comap (RingHom.id R) : Ideal R → Ideal R) = id :=
    funext fun I => comap_id I
  rw [comap_jacobson, hmax]
  calc
    sInf {m : Ideal R | J.comap f ≤ m ∧ m.IsMaximal} =
        sInf (comap (RingHom.id R) '' {m : Ideal R | J.comap f ≤ m ∧ m.IsMaximal}) := by
      rw [hidentity, Set.image_id]
    _ = (J.comap f).jacobson := by
      rw [← comap_jacobson, comap_id]

/-- Extension along an integral homomorphism sends the Jacobson radical of an
ideal into the Jacobson radical of its extension. -/
theorem map_jacobson_le_of_isIntegral (f : R →+* S) (hf : f.IsIntegral)
    (I : Ideal R) : I.jacobson.map f ≤ (I.map f).jacobson := by
  rw [map_le_iff_le_comap, comap_jacobson_of_isIntegral f hf]
  exact jacobson_mono le_comap_map

/-- An integral homomorphism preserves containment in the Jacobson radical of
the zero ideal. -/
theorem map_le_jacobson_bot_of_isIntegral (f : R →+* S) (hf : f.IsIntegral)
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) :
    I.map f ≤ (⊥ : Ideal S).jacobson := by
  calc
    I.map f ≤ (⊥ : Ideal R).jacobson.map f := map_mono hI
    _ ≤ ((⊥ : Ideal R).map f).jacobson := map_jacobson_le_of_isIntegral f hf ⊥
    _ = (⊥ : Ideal S).jacobson := by rw [map_bot]

/-- The commutative-ring case of Mathlib's
`Ideal.comap_jacobson_of_surjective` follows from the integral formula. -/
private theorem comap_jacobson_of_surjective_commRing {f : R →+* S}
    (hf : Function.Surjective f) {J : Ideal S} :
    J.jacobson.comap f = (J.comap f).jacobson := by
  exact comap_jacobson_of_isIntegral f (RingHom.isIntegral_of_surjective f hf) J

end Ideal
