/-
Copyright (c) 2025 Björn H. Wehlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Björn H. Wehlin
-/

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Dirac

import Mathlib.Algebra.Group.Indicator

import Mathlib.Probability.PointProcess.PointMeasure

import Mathlib.Probability.Notation

/-!

!-/

noncomputable section

open MeasureTheory
open MeasureTheory.Measure
open Function
open Set

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace Probability.RandomMeasures

--variable {Ω : Type*} [MeasurableSpace Ω]
--variable {E : Type*} [MeasurableSpace E]

variable {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] {s : Set α} {a : α}

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

set_option diagnostics true

class RandomMeasure {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] where
  distribution : Ω → Measure E
  --measurable_space : MeasurableSpace (Measure E)
  --measurable_distribution : Measurable distribution

class PointProcess₂ {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] extends RandomMeasure where
  is_point_measure_as : μ {ω : Ω | IsPointMeasure (distribution ω)} = 1

class PointProcess {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    extends RandomMeasure Ω E where
  is_point_measure_as : μ {ω : Ω | IsPointMeasure (distribution ω)} = 1

def IsSimplePointProcess {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : PointProcess Ω E μ) : Prop :=
  ∀ ω : Ω, IsPointMeasure (N.distribution ω)

def IsStationary (N : Type*) [PointProcess N] : Prop :=
  sorry

end Probability.RandomMeasures
