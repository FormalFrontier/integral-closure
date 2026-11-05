/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.Polynomial.Div

/-!
# Local normal integral extensions of valuation domains

An integral homomorphism from a valuation domain to a local normal domain makes
the target a valuation domain. The source and target may lie in independent
universes, and the homomorphism need not be injective.

A polynomial over a relatively integrally closed local subring of a field, with a
unit coefficient, can vanish only at an element of the subring or the inverse of
one. The proof descends the coefficients of a linear quotient through Mathlib's
intersection of valuation overrings. Only the final unit argument uses locality.

For the integral-extension criterion, the source image is a valuation domain by
surjective transport, so no injectivity assumption on the original homomorphism
is needed. Algebraicity in the target's fraction field supplies a nonzero
relation. Total divisibility lets us divide all coefficients by one nonzero
coefficient to obtain a relation with coefficient one.

## Limitations

Normality and locality of the target are inputs, not consequences of integrality.
The result does not identify an arbitrary ambient extension field with the
fraction field of an integral closure.

## References

- Mathlib's `Subring.eq_iInf_of_isIntegrallyClosedIn`, the valuation-overring
  intersection theorem (Stacks Project, Tag 090P).
- Mathlib's `Polynomial.coeff_divByMonic_X_sub_C`, for the explicit linear quotient.
- I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition (2002), for the motivating valuation-domain setting. This generic
  criterion is standard commutative algebra, not a reproduction of a particular
  passage or proof of that book.
-/

@[expose] public section

open Polynomial

universe u v

private theorem coeff_mem_of_linear_factor
    {K : Type v} [Field K] (A : Subring K) {F h : K[X]} {z : K}
    (hz : z ≠ 0) (hF : F = (X - C z) * h)
    (hcoeff : ∀ n, F.coeff n ∈ A) (hv : z⁻¹ ∈ A) :
    ∀ n, h.coeff n ∈ A ∧ z * h.coeff n ∈ A := by
  have hzero : z * h.coeff 0 = -F.coeff 0 := by
    rw [hF, sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul]
    ring
  have hsucc (n : ℕ) : z * h.coeff (n + 1) = h.coeff n - F.coeff (n + 1) := by
    rw [hF, sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]
    ring
  have hcancel (a : K) : z⁻¹ * (z * a) = a := by rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]
  intro n
  induction n with
  | zero =>
      have hzh : z * h.coeff 0 ∈ A := hzero.symm ▸ A.neg_mem (hcoeff 0)
      exact ⟨by simpa only [hcancel] using A.mul_mem hv hzh, hzh⟩
  | succ n ih =>
      have hzh : z * h.coeff (n + 1) ∈ A := (hsucc n).symm ▸ A.sub_mem ih.1 (hcoeff _)
      exact ⟨by simpa only [hcancel] using A.mul_mem hv hzh, hzh⟩

private theorem linear_quotient_coeff_mem
    {K : Type v} [Field K] (A : Subring K) [IsIntegrallyClosedIn A K]
    {F : K[X]} {z : K} (hz : z ≠ 0) (hroot : F.IsRoot z)
    (hcoeff : ∀ n, F.coeff n ∈ A) :
    ∀ n, (F /ₘ (X - C z)).coeff n ∈ A ∧ z * (F /ₘ (X - C z)).coeff n ∈ A := by
  have hfactor : F = (X - C z) * (F /ₘ (X - C z)) :=
    (mul_divByMonic_eq_iff_isRoot.mpr hroot).symm
  have hmem (V : ValuationSubring K) (hAV : A ≤ V.toSubring) (n : ℕ) :
      (F /ₘ (X - C z)).coeff n ∈ V ∧ z * (F /ₘ (X - C z)).coeff n ∈ V := by
    rcases V.mem_or_inv_mem z with hzV | hvV
    · have hh : (F /ₘ (X - C z)).coeff n ∈ V := by
        rw [coeff_divByMonic_X_sub_C]
        exact V.toSubring.sum_mem fun i _ =>
          V.mul_mem _ _ (V.toSubring.pow_mem hzV _) (hAV (hcoeff i))
      exact ⟨hh, V.mul_mem _ _ hzV hh⟩
    · exact coeff_mem_of_linear_factor V.toSubring hz hfactor (fun n => hAV (hcoeff n)) hvV n
  intro n
  constructor
  · rw [Subring.eq_iInf_of_isIntegrallyClosedIn (R := A)]
    exact Subring.mem_iInf.mpr fun V => (hmem V.1 V.2 n).1
  · rw [Subring.eq_iInf_of_isIntegrallyClosedIn (R := A)]
    exact Subring.mem_iInf.mpr fun V => (hmem V.1 V.2 n).2

/-- In a local subring integrally closed in its ambient field, a root of a
polynomial with a unit coefficient belongs to the subring or has inverse there.
The unit is required in the coefficient ring, not merely in the ambient field. -/
theorem LocalSubring.mem_or_inv_mem_of_isUnit_coeff
    {K : Type v} [Field K] (A : LocalSubring K) [IsIntegrallyClosedIn A.toSubring K]
    {p : A.toSubring[X]} {z : K} (hroot : p.eval₂ A.toSubring.subtype z = 0)
    {k : ℕ} (hunit : IsUnit (p.coeff k)) :
    z ∈ A.toSubring ∨ z⁻¹ ∈ A.toSubring := by
  by_cases hz : z = 0
  · subst z
    exact Or.inl A.toSubring.zero_mem
  let F := p.map A.toSubring.subtype
  let h := F /ₘ (X - C z)
  have hf : F.IsRoot z := by simpa only [IsRoot, F, eval_map] using hroot
  have hmem := linear_quotient_coeff_mem A.toSubring hz hf (fun n => by simp [F])
  have hfactor : F = (X - C z) * h := (mul_divByMonic_eq_iff_isRoot.mpr hf).symm
  have heq (n : ℕ) : F.coeff (n + 1) = h.coeff n - z * h.coeff (n + 1) := by
    rw [hfactor, sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]
  have hquot (n : ℕ) := (hmem n).1
  have hprod (n : ℕ) := (hmem n).2
  have hinv (n : ℕ) (hu : IsUnit (⟨z * h.coeff n, hprod n⟩ : A.toSubring)) :
      z⁻¹ ∈ A.toSubring := by
    obtain ⟨a, ha⟩ := hu
    have hval : z * h.coeff n = (a : A.toSubring) := congrArg Subtype.val ha.symm
    have hidentity : (h.coeff n : K) * (↑(a⁻¹) : A.toSubring) = z⁻¹ := by
      apply mul_left_cancel₀ hz
      calc
        z * (h.coeff n * (↑(a⁻¹) : A.toSubring)) =
            (↑a : K) * (↑(a⁻¹) : A.toSubring) := by rw [← mul_assoc, hval]
        _ = 1 := congrArg Subtype.val a.val_inv
        _ = z * z⁻¹ := (mul_inv_cancel₀ hz).symm
    exact hidentity ▸ A.toSubring.mul_mem (hquot n) (a⁻¹).val.2
  cases k with
  | zero =>
      have heq0 : p.coeff 0 = -(⟨z * h.coeff 0, hprod 0⟩ : A.toSubring) := by
        apply Subtype.ext
        calc
          (↑(p.coeff 0) : K) = F.coeff 0 := (coeff_map A.toSubring.subtype 0).symm
          _ = -(z * h.coeff 0) := by
            rw [hfactor, sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub]
      exact Or.inr (hinv 0 (by simpa only [heq0, IsUnit.neg_iff] using hunit))
  | succ n =>
      let a : A.toSubring := ⟨h.coeff n, hquot n⟩
      let b : A.toSubring := ⟨z * h.coeff (n + 1), hprod (n + 1)⟩
      have heqD : p.coeff (n + 1) = a - b := by
        apply Subtype.ext
        exact (coeff_map A.toSubring.subtype _).symm.trans (heq n)
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add
          (show IsUnit (a + -b) by simpa only [sub_eq_add_neg, heqD] using hunit) with ha | hb
      · obtain ⟨aunit, hau⟩ := ha
        have hidentity : (z * h.coeff n) * (↑(aunit⁻¹) : A.toSubring) = z := by
          have hauK : (↑aunit : K) = h.coeff n := congrArg Subtype.val hau
          calc
            (z * h.coeff n) * (↑(aunit⁻¹) : A.toSubring) =
                z * ((↑aunit : K) * (↑(aunit⁻¹) : A.toSubring)) := by rw [mul_assoc, hauK]
            _ = z * 1 := congrArg (fun x : K => z * x) (congrArg Subtype.val aunit.val_inv)
            _ = z := mul_one z
        exact Or.inl (hidentity ▸ A.toSubring.mul_mem (hprod n) (aunit⁻¹).val.2)
      · exact Or.inr (hinv (n + 1) ((IsUnit.neg_iff _).mp hb))

private theorem exists_coeff_dvd
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {p : R[X]} (hp : p ≠ 0) :
    ∃ n, p.coeff n ≠ 0 ∧ ∀ j, p.coeff n ∣ p.coeff j := by
  classical
  have hfinite (s : Finset ℕ) :
      s.Nonempty → ∃ n ∈ s, ∀ j ∈ s, p.coeff n ∣ p.coeff j := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s _ ih =>
        intro _
        by_cases hne : s.Nonempty
        · obtain ⟨n, hn, hdiv⟩ := ih hne
          rcases ValuationRing.dvd_total (p.coeff a) (p.coeff n) with han | hna
          · exact ⟨a, Finset.mem_insert_self _ _, fun j hj => by
              rcases Finset.mem_insert.mp hj with rfl | hj
              · exact dvd_refl _
              · exact han.trans (hdiv j hj)⟩
          · exact ⟨n, Finset.mem_insert_of_mem hn, fun j hj => by
              rcases Finset.mem_insert.mp hj with rfl | hj
              · exact hna
              · exact hdiv j hj⟩
        · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
          subst s
          refine ⟨a, by simp, fun j hj => ?_⟩
          have hja : j = a := by simpa using hj
          subst j
          exact dvd_refl _
  obtain ⟨n, hn, hdiv⟩ := hfinite p.support (support_nonempty.mpr hp)
  refine ⟨n, mem_support_iff.mp hn, fun j => ?_⟩
  by_cases hj : j ∈ p.support
  · exact hdiv j hj
  · have heq : p.coeff j = 0 := by
      by_contra hne
      exact hj (mem_support_iff.mpr hne)
    rw [heq]
    exact dvd_zero _

private theorem exists_root_with_unit_coeff
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] (hinj : Function.Injective (algebraMap R K))
    {z : K} (hz : IsAlgebraic R z) :
    ∃ (q : R[X]) (n : ℕ), q.coeff n = 1 ∧ aeval z q = 0 := by
  obtain ⟨p, hp, hroot⟩ := hz
  obtain ⟨n, hn, hdiv⟩ := exists_coeff_dvd hp
  obtain ⟨q, hpq⟩ := (C_dvd_iff_dvd_coeff (p.coeff n) p).mpr hdiv
  have hqn : q.coeff n = 1 := by
    apply mul_left_cancel₀ hn
    simpa only [coeff_C_mul, mul_one] using (congrArg (fun r : R[X] => r.coeff n) hpq).symm
  refine ⟨q, n, hqn, ?_⟩
  rw [hpq, map_mul, aeval_C] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left ((map_ne_zero_iff _ hinj).mpr hn)

/-- An integral homomorphism from a valuation domain to a local normal domain
makes the target a valuation domain. The homomorphism need not be injective,
and neither module finiteness nor algebraicity of a specified ambient field is
an additional hypothesis. -/
theorem RingHom.IsIntegral.isValuationRing_of_isLocalRing
    {R : Type u} {S : Type v}
    [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [IsLocalRing S]
    {f : R →+* S} (hf : f.IsIntegral) : ValuationRing S := by
  let A := f.range
  have : ValuationRing A :=
    Function.Surjective.valuationRing f.rangeRestrict f.rangeRestrict_surjective
  have : Algebra.IsIntegral A S := algebraMap_isIntegral_iff.mp
    (RingHom.IsIntegral.tower_top f.rangeRestrict A.subtype hf)
  let K := FractionRing S
  have : Algebra.IsAlgebraic S K := IsLocalization.isAlgebraic K (nonZeroDivisors S)
  have : Algebra.IsAlgebraic A K := Algebra.IsIntegral.trans_isAlgebraic A S K
  let D := LocalSubring.range (algebraMap S K)
  have hD : D.toSubring = (integralClosure S K).toSubring := by
    rw [IsIntegrallyClosed.integralClosure_eq_bot]
    rfl
  have : IsIntegrallyClosedIn D.toSubring K := by rw [hD]; infer_instance
  let g : A →+* D.toSubring := ((algebraMap S K).comp A.subtype).codRestrict D.toSubring
    (fun a => ⟨a.val, rfl⟩)
  apply (ValuationRing.iff_isInteger_or_isInteger S K).mpr
  intro z
  obtain ⟨q, n, hqn, hroot⟩ := exists_root_with_unit_coeff (R := A)
    ((IsFractionRing.injective S K).comp A.subtype_injective)
    (Algebra.IsAlgebraic.isAlgebraic z)
  have hrootD : (q.map g).eval₂ D.toSubring.subtype z = 0 := by
    rw [eval₂_map]
    change q.eval₂ ((algebraMap S K).comp (algebraMap A S)) z = 0
    rw [← IsScalarTower.algebraMap_eq A S K]
    exact hroot
  have hunit : IsUnit ((q.map g).coeff n) := by rw [coeff_map, hqn, map_one]; exact isUnit_one
  exact D.mem_or_inv_mem_of_isUnit_coeff hrootD hunit
