/-
Copyright (c) 2025 Björn H. Wehlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Björn H. Wehlin
-/

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Defs

import Mathlib.Algebra.Group.Indicator

import Mathlib.Probability.PointProcess.PointMeasure


import Mathlib.Probability.Notation
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Distributions.Uniform

/-!

!-/

noncomputable section

open MeasureTheory
open MeasureTheory.Measure
open Function
open Set

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

open ProbabilityTheory

namespace Probability.RandomMeasures

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [TopologicalSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {κ : Kernel Ω E}

def distribution (κ : Kernel Ω E) (P : Measure Ω) [IsProbabilityMeasure P] : Measure (Measure E) :=
  P.map κ

-- Thanks to Rémy Degenne for help on this
class IsPointProcess (κ : Kernel Ω E) (P : Measure Ω) [IsProbabilityMeasure P] : Prop where
  is_point_measure_as : ∀ᵐ ω ∂P, IsPointMeasure (κ ω)

def evaluation_map (κ : Kernel Ω E) (a : Set E) : Ω → EReal := (fun ν => ν a) ∘ κ

def is_stationary (G : Type*) [Group G] [MulAction G E] [MeasurableConstSMul G E] : Prop :=
  ∀ g : G, P.map ((DomMulAct.mk g) • (⇑κ)) = P.map κ

variable (G : Type*) [AddMonoid G]

noncomputable instance : AddMonoid Gᵈᵐᵃ where
  add := sorry
  add_assoc := sorry
  zero := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := sorry

noncomputable instance : AddAction Gᵈᵐᵃ (Measure E) where
  vadd := sorry
  zero_vadd := sorry
  add_vadd := sorry

def is_stationary_add (G : Type*) [AddGroup G] [AddAction G E] [MeasurableConstVAdd G E] : Prop :=
  ∀ g : G, P.map ((DomAddAct.mk g) +ᵥ (⇑κ)) = P.map κ

def shifted_line_grid : ℝ → Measure ℝ := fun u ↦ PointMeasure (fun (n : ℤ) ↦ n + u)

def k_shifted_line_grid : Kernel ℝ ℝ where
  toFun := fun u ↦ PointMeasure (fun (n : ℤ) ↦ n + u)
  measurable' := by
    intro s hs


variable (U : Ω → ℝ) {h: MeasureTheory.pdf.IsUniform U (Set.Ico 0 1) P}

def unif_shifted_line_grid (X : Ω → ℝ) {h: MeasureTheory.pdf.IsUniform X (Set.Ico 0 1) P}
    : Kernel Ω ℝ where
  toFun := shifted_line_grid ∘ U
  measurable' := by
    apply Measurable.comp
    have : Continuous shifted_line_grid := sorry
    apply Continuous.measurable
    intro s hs

instance amr : AddMonoid ℝ := sorry

#check Multiplicative amr

theorem unif_shifted_line_grid_is_stationary : is_stationary (Multiplicative ℝ) shifted_line_grid := sorry

end Probability.RandomMeasures
