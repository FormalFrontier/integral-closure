/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.Algebra.IsAddUnit
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Regular.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import IntegralClosure.Polynomial
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Integrality and unit reflection along homomorphisms

Power criteria for relative integrality and unit descent from inverse polynomial relations.
The unit descent argument refines the reverse-polynomial argument in Mathlib's
`RingHom.IsIntegral.isLocalHom`, using only a relation at the inverse of the given unit.

Integrality also reflects along homomorphisms of algebras over a commutative base
when each element of the kernel is nilpotent. The algebra rings may be
noncommutative, and the nilpotence exponent may depend on the kernel element;
no vanishing power of the kernel ideal is required.

## References

- Mathlib's `RingHom.IsIntegral.isLocalHom`, for the reverse-polynomial argument.
- `GroupTheory.Algebra.IsAddUnit`, for unit transfer across a zero-sum relation.
- Mathlib's integrality definitions and injective-reflection lemmas
  `isIntegral_algHom_iff` and `Algebra.IsIntegral.of_injective`.
-/

@[expose] public section

universe u v

namespace RingHom

/-- If the inverse of a unit in the image of an injective homomorphism has a monic
polynomial relation over the source, the corresponding source element is a unit.

This is the elementwise semiring form of the reverse-polynomial argument in
`RingHom.IsIntegral.isLocalHom`. Although only semiring instances are required,
the hypotheses force both semirings to admit ring structures. -/
theorem isUnit_of_monic_eval₂_units_inv_eq_zero
    {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →+* S) (hf : Function.Injective f) (r : R) (a : Sˣ)
    (ha : (a : S) = f r) {p : Polynomial R} (hp : p.Monic)
    (hroot : p.eval₂ f (↑(a⁻¹) : S) = 0) : IsUnit r := by
  let _ : Invertible (↑(a⁻¹) : S) := (a⁻¹).invertible
  have hreverse : p.reverse.eval₂ f (a : S) = 0 := by
    simpa only [invOf_units, inv_inv] using
      (Polynomial.eval₂_reverse_eq_zero_iff' f (↑(a⁻¹) : S) p).2 hroot
  have heval : p.reverse.eval r = 0 := by
    apply hf
    simpa only [ha, Polynomial.eval₂_at_apply, map_zero] using hreverse
  have hcoeff : IsUnit (p.reverse.coeff 0) := by
    rw [Polynomial.coeff_zero_reverse, hp.leadingCoeff]
    exact isUnit_one
  have hsum : p.reverse.divX.eval r * r + p.reverse.coeff 0 = 0 := by
    simpa only [Polynomial.eval_add, Polynomial.eval_mul_X, Polynomial.eval_C, heval] using
      congrArg (Polynomial.eval r) (Polynomial.divX_mul_X_add p.reverse)
  have hprod : IsUnit (p.reverse.divX.eval r * r) :=
    (MulHomClass.isUnit_apply_iff_of_add_eq_zero (MulHom.id R) hsum).2 hcoeff
  obtain ⟨s, _, hs⟩ := isUnit_iff_exists.mp hprod
  have hleft : (s * p.reverse.divX.eval r) * r = 1 := by
    simpa only [mul_assoc] using hs
  have hregular : IsRightRegular r := by
    intro x y hxy
    apply hf
    apply (isRegular_iff.mp a.isRegular).2
    simpa only [ha, ← map_mul] using congrArg f hxy
  exact isUnit_iff_exists.mpr
    ⟨s * p.reverse.divX.eval r, hregular.mul_eq_one_symm hleft, hleft⟩

private theorem isLocalHom_of_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (hinj : Function.Injective f) : IsLocalHom f := by
  constructor
  intro r hr
  obtain ⟨a, ha⟩ := hr
  obtain ⟨p, hp, hroot⟩ := hf (↑(a⁻¹) : S)
  exact f.isUnit_of_monic_eval₂_units_inv_eq_zero hinj r a ha hp hroot

/-- A ring homomorphism is integral if every target element has a positive power in its range. -/
theorem isIntegral_of_forall_pow_mem_range
    {R : Type u} {S : Type v} [CommRing R] [Ring S]
    (f : R →+* S)
    (hf : ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range f) : f.IsIntegral := by
  intro x
  obtain ⟨n, hn, r, hr⟩ := hf x
  refine ⟨Polynomial.X ^ n - Polynomial.C r,
    Polynomial.monic_X_pow_sub_C r (ne_of_gt hn), ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hr, sub_self]

/-- An element is integral if one of its positive powers is integral. -/
theorem IsIntegralElem.of_pow
    {R : Type u} {S : Type v} [CommRing R] [Ring S]
    {f : R →+* S} {x : S} {n : ℕ} (hn : 0 < n)
    (hx : f.IsIntegralElem (x ^ n)) : f.IsIntegralElem x := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨Polynomial.expand R n p, (Polynomial.monic_expand_iff hn).2 hp, ?_⟩
  rw [Polynomial.eval₂_expand, hpx]

/-- Every natural power of an integral element is integral. -/
theorem IsIntegralElem.pow
    {R : Type u} {S : Type v} [CommRing R] [Ring S]
    {f : R →+* S} {x : S} (hx : f.IsIntegralElem x) (n : ℕ) :
    f.IsIntegralElem (x ^ n) := by
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨q, hq, hqroot⟩ := IsIntegral.pow (AdjoinRoot.isIntegral_root' hp) n
  have hdiv : p ∣ q.comp (Polynomial.X ^ n) := by
    apply AdjoinRoot.mk_eq_zero.mp
    rw [← AdjoinRoot.aeval_eq]
    exact (Polynomial.eval₂_comp_X_pow (algebraMap R (AdjoinRoot p))
      (AdjoinRoot.root p) n q).trans hqroot
  rcases hdiv with ⟨r, hr⟩
  refine ⟨q, hq, ?_⟩
  rw [← Polynomial.eval₂_comp_X_pow f x n q, hr, mul_comm]
  exact Polynomial.eval₂_mul_eq_zero_of_right' f x r hpx

/-- Integrality is unchanged by taking a positive power. -/
@[simp]
theorem IsIntegralElem.pow_iff
    {R : Type u} {S : Type v} [CommRing R] [Ring S]
    {f : R →+* S} {x : S} {n : ℕ} (hn : 0 < n) :
    f.IsIntegralElem (x ^ n) ↔ f.IsIntegralElem x := by
  exact ⟨IsIntegralElem.of_pow hn, fun hx => IsIntegralElem.pow hx n⟩

end RingHom

/-! ## Integrality reflection for homomorphisms of central algebras -/

section CentralAlgebra

universe w

/-- Integrality reflects along an algebra homomorphism whose kernel elements are
nilpotent. The source and target algebra rings need not be commutative, and the
kernel need not be a nilpotent ideal. -/
theorem IsIntegral.of_isNilpotent_of_map_eq_zero
    {K : Type u} {A : Type v} {B : Type w}
    [CommRing K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (f : A →ₐ[K] B) (hker : ∀ x : A, f x = 0 → IsNilpotent x)
    {a : A} (ha : IsIntegral K (f a)) : IsIntegral K a := by
  obtain ⟨p, hp, hpa⟩ := ha
  have hmap : f (Polynomial.aeval a p) = 0 := by
    rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_def]
    exact hpa
  obtain ⟨n, hn⟩ := hker (Polynomial.aeval a p) hmap
  refine ⟨p ^ n, hp.pow n, ?_⟩
  rw [← Polynomial.aeval_def, map_pow, hn]

/-- An algebra with a homomorphism to an integral algebra is integral if every
element of the kernel is nilpotent. No uniform kernel-ideal exponent is assumed. -/
theorem Algebra.IsIntegral.of_isNilpotent_of_map_eq_zero
    {K : Type u} {A : Type v} {B : Type w}
    [CommRing K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (f : A →ₐ[K] B) (hker : ∀ x : A, f x = 0 → IsNilpotent x)
    [Algebra.IsIntegral K B] : Algebra.IsIntegral K A := by
  refine ⟨fun a => ?_⟩
  exact _root_.IsIntegral.of_isNilpotent_of_map_eq_zero f hker
    (Algebra.IsIntegral.isIntegral (f a))

/-- Injective reflection is the specialization with trivial kernel. -/
private theorem Algebra.IsIntegral.of_injective_via_nil_kernel
    {K : Type u} {A : Type v} {B : Type w}
    [CommRing K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (f : A →ₐ[K] B) (hf : Function.Injective f)
    [Algebra.IsIntegral K B] : Algebra.IsIntegral K A := by
  apply Algebra.IsIntegral.of_isNilpotent_of_map_eq_zero f
  intro x hx
  have hx0 : x = 0 := hf (hx.trans (map_zero f).symm)
  exact ⟨1, by simpa only [pow_one] using hx0⟩

/-- A finite-type source with nil kernel is finite when the target is finite. -/
private theorem Module.Finite.of_finiteType_of_nil_kernel
    {K : Type u} {A : Type v} {B : Type w}
    [CommRing K] [CommRing A] [Ring B] [Algebra K A] [Algebra K B]
    [Algebra.FiniteType K A] [Module.Finite K B]
    (f : A →ₐ[K] B) (hker : ∀ x : A, f x = 0 → IsNilpotent x) :
    Module.Finite K A := by
  let : Algebra.IsIntegral K B := Algebra.IsIntegral.of_finite K B
  let : Algebra.IsIntegral K A :=
    Algebra.IsIntegral.of_isNilpotent_of_map_eq_zero f hker
  exact Algebra.IsIntegral.finite (R := K) (A := A)

end CentralAlgebra
