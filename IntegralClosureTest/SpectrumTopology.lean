/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import IntegralClosure
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Power-image embeddings and the ring homeomorphism criterion

Exponent one recovers the surjective semiring embedding criterion. For rings
with nilpotent kernel, the new embedding and the spectral surjectivity supplied
by Mathlib's `PrimeSpectrum.isHomeomorph_comap` combine through the general
surjective-embedding criterion to give an open map. Both components use the same
original comap and topologies; no additional public homeomorphism wrapper is needed.
The root import supplies the topology API and algebraic injectivity criterion.
-/

universe u v

private theorem isEmbedding_comap_of_surjective
    {A : Type u} {B : Type v} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (hf : Function.Surjective f) :
    Topology.IsEmbedding (PrimeSpectrum.comap f) := by
  apply PrimeSpectrum.isEmbedding_comap_of_forall_pow_mem_range f
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨1, Nat.zero_lt_one, a, (pow_one (f a)).symm⟩

private theorem isOpenMap_comap_of_forall_pow_mem_range
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B)
    (hpow : ∀ b : B, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ Set.range f)
    (hker : RingHom.ker f ≤ nilradical A) : IsOpenMap (PrimeSpectrum.comap f) := by
  have hsurj : Function.Surjective (PrimeSpectrum.comap f) :=
    (PrimeSpectrum.isHomeomorph_comap f hpow hker).surjective
  have hhomeo : IsHomeomorph (PrimeSpectrum.comap f) :=
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨PrimeSpectrum.isEmbedding_comap_of_forall_pow_mem_range f hpow, hsurj⟩
  exact hhomeo.isOpenMap
