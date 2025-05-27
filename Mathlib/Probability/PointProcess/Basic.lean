/-
Copyright (c) 2025 Björn H. Wehlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Björn H. Wehlin
-/

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

import Mathlib.Algebra.Group.Indicator

import Mathlib.Probability.PointProcess.PointMeasure


import Mathlib.Probability.Notation
import Mathlib.Probability.Kernel.Defs

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

--variable {Ω : Type*} [MeasurableSpace Ω]
--variable {E : Type*} [MeasurableSpace E]

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

-- Thanks to Rémy Degenne for help on this
class IsPointProcess (κ : Kernel Ω E) (μ : Measure Ω) : Prop where
  is_point_measure_as : ∀ᵐ ω ∂μ, IsPointMeasure (κ ω)

/-
def IsStationary (N : Ω → Measure E) : Prop :=
  𝔼[evaluation_map] = 0

class PointProcess where
  rv : Ω → Measure E
  is_point_measure_as : μ {ω | IsPointMeasure (rv ω)} = 1

def evaluation_map (N : Ω → Measure E) (a : Set E) : Ω → EReal := (fun ν => ν a) ∘ N

def IsPointProcess (N : Ω → Measure E) : Prop := μ {ω | IsPointMeasure (N ω)} = 1

def IsStationary (N : Ω → Measure E) (h : IsPointProcess N) : Prop :=
  sorry


class PointProcess₁ (Ω E : Type*) [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] where
  rv : Ω → Measure E
  is_point_measure_as : μ {ω | IsPointMeasure (rv ω)} = 1

def evaluation_map₁ (N : PointProcess Ω E μ) (a : Set E) : Ω → EReal := (fun ν => ν a) ∘ N.rv

def evaluation_map (Ω E : Type*) [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (N : PointProcess Ω E μ) (a : Set E) : Ω → EReal := (fun ν => ν a) ∘ N.rv

def intensity_measure (Ω E : Type*) [MeasureSpace Ω] [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (N : PointProcess Ω E μ) (a : Set E) := 𝔼[evaluation_map Ω E μ N a]

def IsStationary (Ω E : Type*) [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (N : PointProcess Ω E μ) (a : Set E) : 𝔼[N.rv a] = 1 Prop :=
  sorry

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
-/
end Probability.RandomMeasures
