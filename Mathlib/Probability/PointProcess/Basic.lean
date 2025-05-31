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

import Mathlib.Data.Real.Basic

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

def my_kernel : Kernel Ω E := sorry
#check ⇑my_kernel


def distribution (κ : Kernel Ω E) (P : Measure Ω) [IsProbabilityMeasure P] : Measure (Measure E) :=
  P.map κ

-- Thanks to Rémy Degenne for help on this
class IsPointProcess (κ : Kernel Ω E) (P : Measure Ω) [IsProbabilityMeasure P] : Prop where
  is_point_measure_as : ∀ᵐ ω ∂P, IsPointMeasure (κ ω)

def evaluation_map (κ : Kernel Ω E) (a : Set E) : Ω → EReal := (fun ν => ν a) ∘ κ

def is_stationary (G : Type*) (κ : Kernel Ω E) (P : Measure Ω)
    [Group G] [MulAction G E] [MeasurableConstSMul G E]
    : Prop :=
  ∀ g : G, P.map ((DomMulAct.mk g) • (⇑κ)) = P.map κ

def shifted_line_grid : ℝ → Measure ℝ := fun u ↦ PointMeasure (fun (n : ℤ) ↦ n + u)

instance : AddCommGroup ℝ := by infer_instance
instance : AddAction ℝ ℝ where
  zero_vadd := by exact fun p ↦ zero_vadd ℝ p
  add_vadd := by exact fun g₁ g₂ p ↦ add_vadd g₁ g₂ p

--variable {U : Ω → ℝ} {h: MeasureTheory.pdf.IsUniform U (Set.Ico 0 1) P}

def randomly_shifted_line_grid (X : Ω → ℝ) : Kernel Ω ℝ where
  toFun := shifted_line_grid ∘ X
  measurable' := by
    apply Measurable.comp
    · sorry
    · exact measurable_generateFrom fun t a ↦ a


theorem unif_shifted_line_grid_is_stationary
  {U : Ω → ℝ} {h: MeasureTheory.pdf.IsUniform U (Set.Ico 0 1) P} :
      is_stationary (Multiplicative ℝ) (randomly_shifted_line_grid U) P := by
  sorry

end Probability.RandomMeasures
