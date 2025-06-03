/-
Copyright (c) 2025 Björn H. Wehlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Björn H. Wehlin
-/

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Count

import Mathlib.Algebra.Group.Indicator

/-!

!-/

noncomputable section

open MeasureTheory
open MeasureTheory.Measure
open Function
open Set

namespace Probability.RandomMeasures

variable {α : Type*} [MeasurableSpace α] {s : Set α} {a : α}

noncomputable def PointMeasure {ι : Type*} (f : ι → α) :
  Measure α := Measure.sum (fun i ↦ Measure.dirac (f i))

def IsPointMeasure {E : Type*} [MeasurableSpace E] (μ : Measure E) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (f : ι → E), μ = PointMeasure f

def IsSimplePointMeasure {S : Set ℕ} (f : S → α)  : Prop :=
    ∀ x : α, PointMeasure f {x} = 0 ∨ PointMeasure f {x} = 1

theorem dirac_on_singleton_iff {a x : α} (hm : MeasurableSet {x}) :
    Measure.dirac a {x} = (1 : ENNReal) ↔ a = x := by
    rw [dirac_eq_one_iff_mem hm]
    exact mem_singleton_iff

theorem is_simple_if_injective {s : Set ℕ} {f : s → α} (hf: Injective f)
    (hm : ∀ x : α, MeasurableSet {x}) :
    IsSimplePointMeasure f := by
  intro x
  simp[PointMeasure]
  by_cases hx : x ∈ (f '' univ)
  ·   have : ∃ i, f i = x := by
          refine SetCoe.exists.mpr ?_
          simp at hx
          exact hx
      obtain ⟨i,hi⟩ := this
      right
      rw [MeasureTheory.Measure.sum_apply _ (hm x), ENNReal.tsum_eq_add_tsum_ite i,
        ENNReal.tsum_eq_zero.mpr, add_zero, dirac_on_singleton_iff (hm x)]
      · assumption
      intro j
      by_cases hj: j = i
      · simp[hj]
      simp[hj]
      have : f j ≠ f i := by
          push_neg at hj
          contrapose! hj
          apply hf
          exact hj
      contrapose! this
      rw[hi]
      rwa [dirac_apply_ne_zero_iff_eq_one, dirac_on_singleton_iff (hm x)] at this

  ·   left
      have : ∀ (i : s), dirac (f i) {x} = 0 := by
          intro i
          contrapose! hx
          rw [dirac_apply_ne_zero_iff_eq_one, dirac_on_singleton_iff (hm x)] at hx
          refine (mem_image f univ x).mpr ?_
          use i
          simp
          exact hx
      intro a as
      specialize this ⟨a, as⟩
      exact this

theorem is_simple_if_injective_iff {S : Set ℕ} {f : S → α} (hm : ∀ x : α, MeasurableSet {x}) :
    Injective f ↔ IsSimplePointMeasure f := by
    constructor
    ·   intro hf
        apply is_simple_if_injective hf hm

    simp[IsSimplePointMeasure]
    intros hsimp i₁ i₂ h
    by_contra hc

    have : dirac (f i₁) {f i₁} = 1 := by exact (dirac_on_singleton_iff (hm (f i₁))).mpr rfl

    have ge_two : PointMeasure f {f i₁} ≥ 2 := by
        simp[PointMeasure]
        rw [MeasureTheory.Measure.sum_apply _ (hm (f i₁)), ENNReal.tsum_eq_add_tsum_ite i₁]
        simp
        rw [ENNReal.tsum_eq_add_tsum_ite i₂]
        push_neg at hc
        symm at hc
        simp[hc]
        rw [← h, this, ← add_assoc, one_add_one_eq_two]
        simp

    specialize hsimp (f i₁)

    have le_two : PointMeasure f {f i₁} ≤ 2 := by
        rcases hsimp with hl | hr
        exact StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a ↦ a) hl 2
        rw[hr]
        exact one_le_two

    have eq_two : PointMeasure f {f i₁} = 2 := by
        apply ge_antisymm
        apply ge_two
        apply le_two

    rcases hsimp with hl | _
    · have : PointMeasure f {f i₁} ≠ 2 := by
        apply ne_of_eq_of_ne hl (by simp)
      contradiction
    · have : PointMeasure f {f i₁} ≠ 1 := by
        apply ne_of_eq_of_ne eq_two (by simp)
      contradiction

theorem sum_eq_sum_without_zeros {ι : Type*} [Countable ι] (s t : Set ι) {f : ι → ENNReal}
  (h : ∀ i : ι, i ∈ s ∨ i ∈ t) (ht : ∀ i ∈ t, f i = 0) :
    ∑' (i : ι), f i = ∑' (i : s), f i + ∑' (i : t), f i := by
  simp [ht]
  refine Eq.symm (tsum_subtype_eq_of_support_subset ?_)
  refine support_subset_iff'.mpr ?_

  intro i hi
  have : i ∈ t := by
    specialize h i
    simp [hi] at h
    assumption

  specialize ht i
  simp[this] at ht
  assumption

theorem pm_iff_integer_valued {μ : Measure α} :
    IsPointMeasure μ ↔ ∀ s : Set α, MeasurableSet s → ∃ n : ℕ∞, μ s = n := by

  constructor
  · intro hpm s hs
    simp [IsPointMeasure] at hpm
    rcases hpm with ⟨ι, hι, f, μdef⟩
    simp [PointMeasure] at μdef
    rw[μdef]
    let t := { i | f i ∈ s }

    have i_in_t_eq_one : ∀ i : ι, i ∈ t ↔ dirac (f i) s = 1 := by
      intro i
      constructor
      exact fun a ↦ dirac_apply_of_mem a
      rw [dirac_eq_one_iff_mem hs]
      exact fun a ↦ a

    have i_in_tc_eq_zero : ∀ i : ι, i ∈ tᶜ → dirac (f i) s = 0 := by
      intro i hi
      rw [dirac_eq_zero_iff_not_mem hs]
      exact hi

    have sdecomp1 : ∑' (i : ι), (dirac (f i)) s = ∑' (i : t), (dirac (f i)) s := by
      rw [sum_eq_sum_without_zeros t tᶜ]
      simp[i_in_tc_eq_zero]
      intro i
      tauto
      intro i
      apply i_in_tc_eq_zero

    have sdecomp2 : ∑' (i : t), (dirac (f i)) s = ∑' (i : t), 1 := by
      refine Eq.symm (tsum_congr ?_)
      intro i
      symm
      rw [dirac_eq_one_iff_mem hs]

      simp[t] at i
      obtain ⟨ _, prop ⟩ := i
      exact prop

    have : (sum (fun i ↦ dirac (f i))) s = ENat.card t := by
      rw[sum_apply _ hs, sdecomp1, sdecomp2]
      exact ENNReal.tsum_one

    use ENat.card t

  · intro h
    simp[IsPointMeasure, PointMeasure]
    sorry
    -- TODO: Prove this (might need more conditions, not sure)



end Probability.RandomMeasures
