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

end Probability.RandomMeasures
