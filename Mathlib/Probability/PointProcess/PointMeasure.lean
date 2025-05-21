/-
Copyright (c) 2025 Björn H. Wehlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Björn H. Wehlin
-/

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

import Mathlib.Algebra.Group.Indicator

noncomputable section

open MeasureTheory
open MeasureTheory.Measure
open Function
open Set

namespace Probability.RandomMeasures

variable {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] {s : Set α} {a : α}

noncomputable def PointMeasure {S : Set ℕ} (f : S → α) :
  Measure α := Measure.sum (fun i ↦ Measure.dirac (f i))

def IsPointMeasure {E : Type*} [MeasurableSpace E] (μ : Measure E) : Prop :=
  ∃ S : Set ℕ, ∃ f : S → E, μ = PointMeasure f

def IsSimplePointMeasure {S : Set ℕ} (f : S → α)  : Prop :=
    ∀ x : α, PointMeasure f {x} = 0 ∨ PointMeasure f {x} = 1

@[simp]
theorem dirac_on_singleton_of_singleton_eq_one {x : α} (hm : MeasurableSet {x}) :
    Measure.dirac x {x} = (1 : ENNReal) := by
    rw [Measure.dirac_apply' x hm]
    exact (indicator_eq_one_iff_mem ENNReal).mpr rfl

theorem dirac_on_singleton_iff {a x : α} (hm : MeasurableSet {x}) :
    Measure.dirac a {x} = (1 : ENNReal) ↔ a = x := by
    constructor
    ·   intro h
        rwa [Measure.dirac_apply' a hm, indicator_eq_one_iff_mem] at h
    ·   intro h
        rw[h]
        apply dirac_on_singleton_of_singleton_eq_one
        apply hm

theorem point_measure_self_apply_gt {S : Set ℕ} {f : S → α} (hm : ∀ x : α, MeasurableSet {x}) :
    ∀ (i : S), PointMeasure f {f i} > 0 := by
  intro i
  simp[PointMeasure]
  rw [MeasureTheory.Measure.sum_apply _ (hm (f i)), ENNReal.tsum_eq_add_tsum_ite i,
    dirac_on_singleton_of_singleton_eq_one (hm (f i))]
  simp

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
      rwa [dirac_apply'_ne_zero_iff_eq_one _ (hm x), dirac_on_singleton_iff (hm x)] at this

  ·   left
      have : ∀ (i : s), dirac (f i) {x} = 0 := by
          intro i
          contrapose! hx
          rw [dirac_apply'_ne_zero_iff_eq_one _ (hm x), dirac_on_singleton_iff (hm x)] at hx
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

    have : dirac (f i₁) {f i₁} = 1 := by exact
      dirac_on_singleton_of_singleton_eq_one (hm (f i₁))

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

theorem time_seq (μ : Measure ℝ) (h : IsPointMeasure μ) [IsLocallyFiniteMeasure μ] :
    ∃ f : ℤ → EReal,
      f 0 ≤ 0
      ∧ 0 < f 1
      ∧ ∀ m n : ℤ, m < n → f m ≤ f n
      ∧ (∀ s : Set ℝ, Measurable s → μ s =
        ∑' n : ℤ, if ((f n) = ⊤ ∨ (f n) = ⊥) then 0 else dirac (EReal.toReal (f n)) s) := by
    sorry

end Probability.RandomMeasures
