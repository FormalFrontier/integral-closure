/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Finiteness over power-containing subalgebras

A commutative semiring algebra is finite over a subalgebra containing a positive
power of each member of a finite algebra-generating set. The exponent may depend
on the generator, and the scalar action is the canonical inclusion action.

Consequently, a finite-type commutative semiring algebra is finite over any
subalgebra containing a positive power of each element. Neither finite type of
the subalgebra over the original base nor a common exponent is required.

The argument bounds the powers in each singleton adjoin, then combines finitely
many such spans using products of submodules. It requires no subtraction or
integrality criterion.

## References

- Mathlib's `Algebra.adjoin_eq_span` and `Algebra.adjoin_union_coe_submodule`
- Mathlib's `Submodule.FG.mul`
-/

@[expose] public section

universe u v

private theorem fg_adjoin_singleton_of_pow_mem
    {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (C : Subalgebra R A) (x : A) (n : ℕ) (hn : 0 < n) (hx : x ^ n ∈ C) :
    (Algebra.adjoin C ({x} : Set A)).toSubmodule.FG := by
  classical
  let s : Finset A := (Finset.range n).image (fun k => x ^ k)
  have hpow : ∀ k : ℕ, x ^ k ∈ Submodule.span C (s : Set A) := by
    intro k
    have hrem : x ^ (k % n) ∈ Submodule.span C (s : Set A) := by
      apply Submodule.subset_span
      exact Finset.mem_image.mpr
        ⟨k % n, Finset.mem_range.mpr (Nat.mod_lt k hn), rfl⟩
    have hreduce :
        ((⟨x ^ n, hx⟩ : C) ^ (k / n)) • x ^ (k % n) = x ^ k := by
      rw [Algebra.smul_def, map_pow, Subalgebra.algebraMap_apply,
        ← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [← hreduce]
    exact (Submodule.span C (s : Set A)).smul_mem _ hrem
  have hspan :
      (Algebra.adjoin C ({x} : Set A)).toSubmodule =
        Submodule.span C (Set.range (fun k : ℕ => x ^ k)) := by
    rw [Algebra.adjoin_eq_span, ← Submonoid.powers_eq_closure,
      Submonoid.coe_powers]
  have hbounded :
      Submodule.span C (Set.range (fun k : ℕ => x ^ k)) =
        Submodule.span C (s : Set A) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro y ⟨k, rfl⟩
      exact hpow k
    · apply Submodule.span_mono
      intro y hy
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨k, rfl⟩
  rw [hspan, hbounded]
  exact Submodule.fg_span s.finite_toSet

private theorem fg_adjoin_finset_of_forall_exists_pow_mem
    {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (C : Subalgebra R A) (s : Finset A)
    (hpow : ∀ x ∈ s, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ C) :
    (Algebra.adjoin C (s : Set A)).toSubmodule.FG := by
  classical
  revert hpow
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa only [Finset.coe_empty, Algebra.adjoin_empty] using
      (Subalgebra.fg_bot_toSubmodule (R := C) (A := A))
  · intro x t _ ih ht
    obtain ⟨n, hn, hxn⟩ := ht x (Finset.mem_insert_self x t)
    have hfgt : (Algebra.adjoin C (t : Set A)).toSubmodule.FG :=
      ih fun y hy => ht y (Finset.mem_insert_of_mem hy)
    rw [Finset.coe_insert, ← Set.singleton_union,
      Algebra.adjoin_union_coe_submodule C ({x} : Set A) (t : Set A)]
    exact (fg_adjoin_singleton_of_pow_mem C x n hn hxn).mul hfgt

/-- A commutative semiring algebra is finite over a subalgebra containing a
positive power of each member of a finite algebra-generating set. -/
theorem Subalgebra.finite_of_adjoin_eq_top_of_forall_exists_pow_mem
    {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (C : Subalgebra R A) (s : Finset A)
    (hs : Algebra.adjoin R (s : Set A) = ⊤)
    (hpow : ∀ x ∈ s, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ C) : Module.Finite C A := by
  have hle : Algebra.adjoin R (s : Set A) ≤
      Subalgebra.restrictScalars R (Algebra.adjoin C (s : Set A)) := by
    apply (Algebra.adjoin_le _ : Algebra.adjoin R (s : Set A) ≤
      Subalgebra.restrictScalars R (Algebra.adjoin C (s : Set A)))
    simp only [Subalgebra.coe_restrictScalars]
    exact Algebra.subset_adjoin
  have htop : Algebra.adjoin C (s : Set A) = ⊤ :=
    Algebra.eq_top_iff.mpr fun a => hle (Algebra.eq_top_iff.mp hs a)
  apply Module.Finite.of_fg_top
  simpa only [htop, Algebra.top_toSubmodule] using
    (fg_adjoin_finset_of_forall_exists_pow_mem C s hpow)

/-- A finite-type commutative semiring algebra is finite over a subalgebra
containing a positive power of every element. Neither finite type of the
subalgebra over the original base nor a common exponent is required. -/
theorem Subalgebra.finite_of_forall_exists_pow_mem
    {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [Algebra.FiniteType R A]
    (C : Subalgebra R A)
    (hpow : ∀ a : A, ∃ n : ℕ, 0 < n ∧ a ^ n ∈ C) : Module.Finite C A := by
  obtain ⟨s, hs⟩ := (‹Algebra.FiniteType R A›).out
  exact Subalgebra.finite_of_adjoin_eq_top_of_forall_exists_pow_mem C s hs
    (fun x _ => hpow x)
