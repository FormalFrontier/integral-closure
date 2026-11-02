/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

public import IntegralClosure.LinearRetract
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Scalar extension: normal-domain descent and prime-power images

For a field extension `l/k` and a commutative `k`-algebra `A`, this file proves
that the domain and integral-closedness properties of `A ⊗[k] l` descend to
`A`. No finite-dimensionality, algebraicity or separability hypothesis on
`l/k` is needed; k, l and A live in independent universes. The two descent
claims are separate theorems, not global instances.

For algebras over a commutative semiring, elementwise prime-power membership
in the image of an algebra homomorphism is preserved by scalar extension when
the prime vanishes in the target. The domain of the homomorphism need only be
a semiring. The canonical algebra-map case is obtained by the right unit-tensor
equivalence. All exponents may depend on the element, and zero semirings are
included.

The prime-power argument follows the tensor-induction approach of Mathlib's
`IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar`,
formalized by Jz Pan, using the prime-power binomial identity without imposing
exponential-characteristic classes.

## References

- Mathlib's `IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar`
- Mathlib's `exists_add_pow_prime_pow_eq`
- Mathlib's `Algebra.TensorProduct.map` and `Algebra.TensorProduct.rid`
-/

set_option warningAsError true

noncomputable section

public section

open scoped TensorProduct

universe u v w

namespace Algebra.TensorProduct

variable (k : Type u) (l : Type v) (A : Type w)
  [Field k] [Field l] [CommRing A] [Algebra k l] [Algebra k A]

/-- Applying any k-linear functional `f : l →ₗ[k] k` to the right factor gives an
A-linear map from `A ⊗[k] l` back to A. It evaluates `a ⊗ₜ[k] b` as
`a * algebraMap k A (f b)`; neither `f 1 = 1` nor multiplicativity is needed.
The definition is noncomputable and exposed for downstream simplification; the
pure-tensor calculation follows from its universal-property construction, not
from an advertised definitional equality. -/
@[expose]
def rightLinearMap (f : l →ₗ[k] k) : A ⊗[k] l →ₗ[A] A :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun a ↦ a • ((Algebra.linearMap k A).comp f)
      map_add' := fun a b ↦ by simp [add_smul]
      map_smul' := fun a b ↦ by simp [mul_smul] }

/-- If the functional sends `1` to `1`, evaluating after `includeLeft` is the
identity on A. This supplies the A-linear left inverse used in descent; it does
not assert that `rightLinearMap` preserves multiplication. -/
theorem rightLinearMap_includeLeft (f : l →ₗ[k] k) (hf : f 1 = 1) (a : A) :
    rightLinearMap k l A f (includeLeft (R := k) (S := A) (A := A) (B := l) a) = a := by
  simp [rightLinearMap, includeLeft_apply, hf]

/-- If a scalar extension of a commutative algebra along a field extension is a
domain, then the original algebra is a domain, by injectivity of `includeLeft`.
This theorem returns a typeclass proof; it installs no global instance. -/
theorem isDomain_left [IsDomain (A ⊗[k] l)] : IsDomain A :=
  (includeLeft_injective (S := A) (algebraMap k l).injective).isDomain
    (includeLeft (R := k) (S := A) (A := A) (B := l)).toRingHom

/-- If a scalar extension of a commutative algebra along a field extension is
an integrally closed domain, then the original algebra is integrally closed.
Projective-module duality supplies a k-linear functional with `f 1 = 1` for any
field extension; `rightLinearMap_includeLeft` and the generic linear-retraction
theorem give descent. No finite-dimensionality or multiplicative retraction is
needed, and this theorem installs no global instance. -/
theorem isIntegrallyClosed_left
    [IsDomain (A ⊗[k] l)] [IsIntegrallyClosed (A ⊗[k] l)] :
    IsIntegrallyClosed A := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k (x := (1 : l)) one_ne_zero
  exact IsIntegrallyClosed.of_linearRetract
    (includeLeft_injective (S := A) (algebraMap k l).injective)
    (rightLinearMap k l A f) (rightLinearMap_includeLeft k l A f hf)

end Algebra.TensorProduct

@[expose] public section

universe u₁

namespace Algebra.TensorProduct

section CommSemiring

/-- Elementwise prime-power membership in the image of an algebra homomorphism
is preserved by scalar extension when the prime vanishes in the target. The
exponent may depend on the tensor element. The domain need not be commutative. -/
theorem exists_pow_pow_mem_range_map
    {A : Type u} {B : Type v} {C : Type w} {D : Type u₁}
    [CommSemiring A] [Semiring B] [CommSemiring C] [CommSemiring D]
    [Algebra A B] [Algebra A C] [Algebra A D]
    (f : B →ₐ[A] D) (p : ℕ) (hp : p.Prime) (hD : (p : D) = 0)
    (hpow : ∀ d : D, ∃ r : ℕ, d ^ (p ^ r) ∈ Set.range f)
    (x : C ⊗[A] D) :
    ∃ s : ℕ, x ^ (p ^ s) ∈ Set.range (map (AlgHom.id C C) f) := by
  -- Transport cast vanishing along the original right inclusion.
  have hT : (p : C ⊗[A] D) = 0 := by
    simpa only [map_natCast, map_zero] using
      congrArg (includeRight : D →ₐ[A] C ⊗[A] D) hD
  induction x using TensorProduct.inductionOn with
  | tmul c d =>
    obtain ⟨r, b, hb⟩ := hpow d
    refine ⟨r, (c ^ (p ^ r)) ⊗ₜ[A] b, ?_⟩
    simp only [map_tmul, AlgHom.id_apply, tmul_pow, hb]
  | add x y hx hy =>
    obtain ⟨r, u, hu⟩ := hx
    obtain ⟨s, v, hv⟩ := hy
    obtain ⟨z, hz⟩ := exists_add_pow_prime_pow_eq hp x y (r + s)
    have hadd : (x + y) ^ (p ^ (r + s)) =
        x ^ (p ^ (r + s)) + y ^ (p ^ (r + s)) := by
      simpa only [hT, zero_mul, add_zero] using hz
    -- Synchronize exponents without commuting the source witnesses.
    refine ⟨r + s, u ^ (p ^ s) + v ^ (p ^ r), ?_⟩
    calc
      map (AlgHom.id C C) f (u ^ (p ^ s) + v ^ (p ^ r)) =
          x ^ (p ^ r * p ^ s) + y ^ (p ^ s * p ^ r) := by
        rw [map_add, map_pow, map_pow, hu, hv, ← pow_mul, ← pow_mul]
      _ = x ^ (p ^ (r + s)) + y ^ (p ^ (r + s)) := by
        rw [← pow_add, ← pow_add, Nat.add_comm s r]
      _ = (x + y) ^ (p ^ (r + s)) := hadd.symm

/-- Tensoring the canonical algebra map with the identity, after the inverse
right unit-tensor equivalence, gives the canonical algebra map over the new scalars. -/
theorem map_id_ofId_comp_rid_symm
    {A : Type u} {B : Type v} {C : Type w}
    [CommSemiring A] [Semiring B] [CommSemiring C]
    [Algebra A B] [Algebra A C] :
    (map (AlgHom.id C C) (Algebra.ofId A B)).comp
        (Algebra.TensorProduct.rid A C C).symm.toAlgHom =
      Algebra.ofId C (C ⊗[A] B) := by
  exact Algebra.ext_id (R := C) (A := C ⊗[A] B) _ _

/-- If every element of an algebra has a `p ^ r`-power in the scalar image
for some `r`, and the prime `p` vanishes in that algebra, then the same holds
for the canonical scalar map after arbitrary commutative-semiring base change.
The right unit-tensor equivalence identifies the source with the new scalars. -/
theorem exists_pow_pow_mem_range_algebraMap
    {A : Type u} {B : Type v} {C : Type w}
    [CommSemiring A] [CommSemiring B] [CommSemiring C]
    [Algebra A B] [Algebra A C]
    (p : ℕ) (hp : p.Prime) (hB : (p : B) = 0)
    (hpow : ∀ b : B, ∃ r : ℕ, b ^ (p ^ r) ∈ Set.range (algebraMap A B))
    (x : C ⊗[A] B) :
    ∃ s : ℕ, x ^ (p ^ s) ∈ Set.range (algebraMap C (C ⊗[A] B)) := by
  obtain ⟨s, y, hy⟩ :=
    exists_pow_pow_mem_range_map (C := C) (Algebra.ofId A B) p hp hB hpow x
  refine ⟨s, (Algebra.TensorProduct.rid A C C) y, ?_⟩
  calc
    algebraMap C (C ⊗[A] B) ((Algebra.TensorProduct.rid A C C) y) =
        map (AlgHom.id C C) (Algebra.ofId A B)
          ((Algebra.TensorProduct.rid A C C).symm
            ((Algebra.TensorProduct.rid A C C) y)) :=
      (congrArg
        (fun g : C →ₐ[C] C ⊗[A] B ↦ g ((Algebra.TensorProduct.rid A C C) y))
        (map_id_ofId_comp_rid_symm (A := A) (B := B) (C := C))).symm
    _ = map (AlgHom.id C C) (Algebra.ofId A B) y := by
      rw [AlgEquiv.symm_apply_apply]
    _ = x ^ (p ^ s) := hy

end CommSemiring

end Algebra.TensorProduct

end
