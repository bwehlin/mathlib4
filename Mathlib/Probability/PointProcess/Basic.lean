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


variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [TopologicalSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P]

def distribution (κ : Kernel Ω E) (P : Measure Ω) [IsProbabilityMeasure P] : Measure (Measure E) :=
  P.map κ

-- Thanks to Rémy Degenne for help on this
class IsPointProcess (κ : Kernel Ω E) (P : Measure Ω) [IsProbabilityMeasure P] : Prop where
  is_point_measure_as : ∀ᵐ ω ∂P, IsPointMeasure (κ ω)

def evaluation_map (κ : Kernel Ω E) (a : Set E) : Ω → EReal := (fun ν => ν a) ∘ κ

theorem MeasureTheory.integral_domSMul{E : Type u_2} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Type*} {A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] [MeasurableSpace A] [MeasurableConstSMul G A] {μ : Measure A} (g : Gᵈᵐᵃ) (f : A → E) :
    ∫ (x : A), f x ∂g • μ = ∫ (x : A), f ((DomMulAct.mk.symm g)⁻¹ • x) ∂μ := by
  #check (DomMulAct.mk.symm g)⁻¹
  #check DomMulAct.mk.symm g
  sorry

instance {G : Type*} [Group G] [MulAction G E] : MulAction G (Measure E) where
  smul := fun g μ => μ.map (fun x => g • x)
  one_smul := by
    intro μ
    simp only [HSMul.hSMul]



    -- example: this is OK
    have : ∀ x : E, (1 : G) • x = x := by
      intro x
      exact MulAction.one_smul x

    -- example: don't know where to go from here
    have : ∀ x : E, SMul.smul (1 : G) x = x := by
      intro x



  mul_smul := sorry

-- MeasureTheory.Measure.IsMulLeftInvariant
def IsStationary (κ : Kernel Ω E) (P : Measure Ω) (f : E → E) [IsProbabilityMeasure P] [IsPointProcess κ P]
  {G : Type*} [Group G] [MulAction G (Measure E)] [MeasurableSpace G]
    : Prop :=
  SMulInvariantMeasure G (P.map κ)
  --∀ g : G, ∀ s : Set E, (P.map κ) s = (P.map κ ) s


variable (κ : Kernel Ω E)
#check κ.toFun
#check ⇑κ
#check ↑κ
#check P.map (κ.toFun)
#check P.map κ
#check P.map ⇑κ

def IsGroupInvariant {E : Type*} [MeasurableSpace E] (μ : Measure E) {G : Type*} (g : G)
    [Group G] [MulAction G (Set E)] : Prop :=
  ∀ s : Set E, MeasurableSet s → μ s = μ (g • s)

def IsStationary (κ : Kernel Ω E) (P : Measure Ω) [IsProbabilityMeasure P] {G : Type*} (g : G)
    [Group G] [MulAction G (Set E)] : Prop :=


def IsStationary (κ : Kernel Ω E) (P : Measure Ω) [IsProbabilityMeasure P] [IsPointProcess κ P]
    : Prop :=
  sorry

--def local_evaluation_map (κ : Kernel Ω E) ()

--theorem evaluation_map_is_measurable (κ : Kernel Ω E) (a : Set E) :

def IsStationary {E : Type*} [MeasurableSpace E] [TopologicalSpace E] (h : LocallyFinite E) (κ : Kernel Ω E) : Prop :=
  𝔼[evaluation_map] = 0


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
