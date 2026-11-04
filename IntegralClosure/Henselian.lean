/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import AdicModules.Polynomial.Hensel
import Mathlib.Tactic

/-!
# Integral domains over Henselian local rings

An integral domain integral over a commutative Henselian local ring is local.
The base need not be a domain, and the structural homomorphism need not be
injective. The extension need not be finite as a module.

The proof lifts coprime monic residue factors of an annihilating polynomial
of a single element. Maximal-ideal contraction then compares its evaluations
at zero and one, without identifying residue fields of different rings.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
  second edition, 2002.
* Formal Frontier, [Adic Modules](https://github.com/FormalFrontier/adic-modules),
  `AdicModules.Polynomial.Hensel`, for monic coprime-factor lifting.
-/

@[expose] public section

open Polynomial

universe u v

namespace Polynomial

private theorem exists_X_pow_mul_constant_nonzero
    {R : Type u} [Semiring R] (p : R[X]) (hp : p ≠ 0) :
    ∃ n : ℕ, ∃ q : R[X], p = X ^ n * q ∧ q.coeff 0 ≠ 0 := by
  classical
  cases subsingleton_or_nontrivial R with
  | inl hR =>
    have : Subsingleton R := hR
    exact False.elim (hp (by ext i; exact Subsingleton.elim _ _))
  | inr hR =>
    have : Nontrivial R := hR
    have hfactor : ∀ d : ℕ, ∀ f : R[X], f.natDegree = d → f ≠ 0 →
        ∃ n : ℕ, ∃ q : R[X], f = X ^ n * q ∧ q.coeff 0 ≠ 0 := by
      intro d
      induction d using Nat.strong_induction_on with
      | h d ih =>
        intro f hfd hf
        by_cases hf0 : f.coeff 0 = 0
        · have hdiv : (X : R[X]) ∣ f := X_dvd_iff.mpr hf0
          obtain ⟨q, hfq⟩ := hdiv
          have hq : q ≠ 0 := by
            intro hq0
            apply hf
            simpa only [hq0, mul_zero] using hfq
          have hdegree : f.natDegree = q.natDegree + 1 := by
            rw [hfq]
            exact natDegree_X_mul hq
          have hlt : q.natDegree < d := by omega
          obtain ⟨n, r, hqr, hr0⟩ := ih q.natDegree hlt q rfl hq
          refine ⟨n + 1, r, ?_, hr0⟩
          calc
            f = (X : R[X]) * q := hfq
            _ = (X : R[X]) * (X ^ n * r) := by rw [hqr]
            _ = (X : R[X]) ^ (n + 1) * r := by
              simp only [pow_succ', mul_assoc]
        · refine ⟨0, f, ?_, hf0⟩
          simp only [pow_zero, one_mul]
    exact hfactor p.natDegree p rfl hp

private theorem isCoprime_X_of_unit_constant
    {R : Type u} [CommRing R] (q : R[X]) (hq : IsUnit (q.coeff 0)) :
    IsCoprime (X : R[X]) q := by
  have hdiv : (X : R[X]) ∣ q - C (q.coeff 0) := by
    apply X_dvd_iff.mpr
    simp
  obtain ⟨r, hr⟩ := hdiv
  rcases hq with ⟨u, hu⟩
  have hinv : (C (↑(u⁻¹) : R) : R[X]) * C (q.coeff 0) = 1 := by
    rw [← hu, ← map_mul]
    simp
  refine ⟨-C (↑(u⁻¹) : R) * r, C (↑(u⁻¹) : R), ?_⟩
  calc
    (-C (↑(u⁻¹) : R) * r) * X + C (↑(u⁻¹) : R) * q =
        C (↑(u⁻¹) : R) * (q - X * r) := by ring
    _ = C (↑(u⁻¹) : R) * C (q.coeff 0) := by
      rw [← hr]
      ring
    _ = 1 := hinv

private theorem residue_eval_eq_zero
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (m : Ideal R) (J : Ideal S)
    (hc : J.comap (algebraMap R S) = m)
    (x : S) (r : R) (hxr : x - algebraMap R S r ∈ J)
    (p : R[X]) (hp : aeval x p = 0) :
    (p.map (Ideal.Quotient.mk m)).eval ((Ideal.Quotient.mk m) r) = 0 := by
  let φ : S →+* (S ⧸ J) := Ideal.Quotient.mk J
  let ρ : R →+* (R ⧸ m) := Ideal.Quotient.mk m
  have hsub : φ (x - algebraMap R S r) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).2 hxr
  have hpoint : φ x = φ (algebraMap R S r) := by
    simpa only [map_sub, sub_eq_zero] using hsub
  have heval :
      φ.comp (aeval x).toRingHom =
        (φ.comp (algebraMap R S)).comp (evalRingHom r) := by
    ext a <;> simp [RingHom.comp_apply, hpoint]
  have hvalue : φ (aeval x p) = φ (algebraMap R S (p.eval r)) := by
    simpa [RingHom.comp_apply] using
      congrArg (fun F : R[X] →+* (S ⧸ J) => F p) heval
  have hzero : φ (algebraMap R S (p.eval r)) = 0 := by
    calc
      φ (algebraMap R S (p.eval r)) = φ (aeval x p) := hvalue.symm
      _ = 0 := by simp only [hp, map_zero]
  have hmemJ : algebraMap R S (p.eval r) ∈ J :=
    (Ideal.Quotient.eq_zero_iff_mem).1 hzero
  have hmemm : p.eval r ∈ m := by
    rw [← hc]
    exact hmemJ
  have hbasezero : ρ (p.eval r) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).2 hmemm
  calc
    (p.map (Ideal.Quotient.mk m)).eval ((Ideal.Quotient.mk m) r)
        = ρ (p.eval r) := by simp [ρ]
    _ = 0 := hbasezero

end Polynomial

namespace HenselianLocalRing

/-- An integral domain integral over a Henselian local ring is local.
The base may have zero divisors or nilpotents; this generalizes the valuation-ring
setting of Fesenko–Vostokov, *Local Fields and Their Extensions*. -/
theorem isLocalRing_of_isIntegral
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [HenselianLocalRing R] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] : IsLocalRing S := by
  classical
  let m : Ideal R := IsLocalRing.maximalIdeal R
  have : m.IsMaximal := by
    dsimp [m]
    infer_instance
  let κ : Type u := R ⧸ m
  let ρ : R →+* κ := Ideal.Quotient.mk m
  have hcontract (J : Ideal S) [J.IsMaximal] :
      J.comap (algebraMap R S) = m := by
    have hJ : (J.comap (algebraMap R S)).IsMaximal := by
      exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal J
    exact (IsLocalRing.isMaximal_iff R).mp hJ
  refine { toNontrivial := inferInstance, isUnit_or_isUnit_of_add_one := ?_ }
  intro a b hab
  by_contra hnot
  have ha : ¬ IsUnit a := fun ha => hnot (Or.inl ha)
  have hb : ¬ IsUnit b := fun hb => hnot (Or.inr hb)
  obtain ⟨M, hM, haM⟩ := exists_max_ideal_of_mem_nonunits ha
  obtain ⟨N, hN, hbN⟩ := exists_max_ideal_of_mem_nonunits hb
  have : M.IsMaximal := hM
  have : N.IsMaximal := hN
  have hMcontract : M.comap (algebraMap R S) = m := hcontract M
  have hNcontract : N.comap (algebraMap R S) = m := hcontract N
  have haIntegral : IsIntegral R a := Algebra.IsIntegral.isIntegral a
  have hpoly : ∃ f : R[X], f.Monic ∧ aeval a f = 0 := by
    exact (Set.mem_image (⇑(aeval a)) (fun x => x.leadingCoeff = 1) 0).mp haIntegral
  obtain ⟨f, hf, hfa⟩ := hpoly
  have hfbar : (f.map ρ).Monic := hf.map ρ
  obtain ⟨n, q, hsplit, hq0⟩ :=
    Polynomial.exists_X_pow_mul_constant_nonzero (f.map ρ) hfbar.ne_zero
  have hqMonic : q.Monic := by
    rw [hsplit] at hfbar
    exact Monic.of_mul_monic_left (monic_X_pow n) hfbar
  have hunit : IsUnit (q.coeff 0) := by
    have hsurj : Function.Surjective (Ideal.Quotient.mk m) := by
      apply Ideal.Quotient.mk_surjective
    obtain ⟨r, hr⟩ := hsurj (q.coeff 0)
    have hrunit : IsUnit r := by
      by_contra hrnonunit
      obtain ⟨J, hJ, hrJ⟩ := exists_max_ideal_of_mem_nonunits hrnonunit
      have hJm : J = m := (IsLocalRing.isMaximal_iff R).mp hJ
      have hrm : r ∈ m := by
        simpa only [hJm] using hrJ
      have hzero : (Ideal.Quotient.mk m) r = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).2 hrm
      exact hq0 (hr.symm.trans hzero)
    have hquotunit : IsUnit ((Ideal.Quotient.mk m) r) :=
      hrunit.map (Ideal.Quotient.mk m)
    exact hr ▸ hquotunit
  have hcopX : IsCoprime (X : κ[X]) q :=
    Polynomial.isCoprime_X_of_unit_constant q hunit
  have hcop : IsCoprime ((X : κ[X]) ^ n) q := IsCoprime.pow_left hcopX
  have hX : ((X : κ[X]) ^ n).Monic := monic_X_pow n
  have hfactor : ∃ G H : R[X], G.Monic ∧ H.Monic ∧ f = G * H ∧
      G.map ρ = (X : κ[X]) ^ n ∧ H.map ρ = q := by
    apply HenselianRing.exists_monic_factorization (I := m) <;> assumption
  obtain ⟨G, H, _hGMonic, _hHMonic, hfac, hGred, hHred⟩ := hfactor
  have haM0 : a - algebraMap R S (0 : R) ∈ M := by
    simpa using haM
  have haN1 : a - algebraMap R S (1 : R) ∈ N := by
    have haeq : a - algebraMap R S (1 : R) = -b := by
      calc
        a - algebraMap R S (1 : R) = a - 1 := by simp
        _ = a - (a + b) := congrArg (fun z : S => a - z) hab.symm
        _ = -b := by ring
    rw [haeq]
    exact N.neg_mem hbN
  have hHne : aeval a H ≠ 0 := by
    intro hHa
    have hH0 : (H.map ρ).eval 0 = 0 := by
      simpa [ρ] using
        (Polynomial.residue_eval_eq_zero m M hMcontract a 0 haM0 H hHa)
    rw [hHred] at hH0
    exact hq0 ((coeff_zero_eq_eval_zero q).trans hH0)
  have hproduct : aeval a G * aeval a H = 0 := by
    calc
      aeval a G * aeval a H = aeval a (G * H) := (map_mul (aeval a) G H).symm
      _ = aeval a f := congrArg (aeval a) hfac.symm
      _ = 0 := hfa
  have hGa : aeval a G = 0 := (mul_eq_zero.mp hproduct).resolve_right hHne
  have hG1 : (G.map ρ).eval 1 = 0 := by
    simpa [ρ] using
      (Polynomial.residue_eval_eq_zero m N hNcontract a 1 haN1 G hGa)
  rw [hGred] at hG1
  simp at hG1

end HenselianLocalRing

namespace RingHom

/-- An integral unital homomorphism from a Henselian local ring to an integral
domain has local codomain; the homomorphism need not be injective. -/
theorem isLocalRing_of_henselian_of_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [HenselianLocalRing R] [IsDomain S]
    (α : R →+* S) (hα : α.IsIntegral) : IsLocalRing S := by
  let : Algebra R S := α.toAlgebra
  have : Algebra.IsIntegral R S := algebraMap_isIntegral_iff.mp hα
  exact HenselianLocalRing.isLocalRing_of_isIntegral R S

end RingHom
