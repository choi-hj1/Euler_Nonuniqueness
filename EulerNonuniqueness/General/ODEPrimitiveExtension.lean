import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

def odePrimitiveExtension (trajectory velocity : ℝ → Space) (time : ℝ) : Space :=
  trajectory 0 + ∫ current in (0 : ℝ)..time, velocity current

theorem odePrimitiveExtension_hasDerivAt (trajectory velocity : ℝ → Space)
    (velocityContinuous : Continuous velocity) (time : ℝ) :
    HasDerivAt (odePrimitiveExtension trajectory velocity) (velocity time) time := by
  exact (intervalIntegral.integral_hasDerivAt_right (velocityContinuous.intervalIntegrable 0 time)
    velocityContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter velocityContinuous.continuousAt).const_add _

theorem odePrimitiveExtension_continuous (trajectory velocity : ℝ → Space)
    (velocityContinuous : Continuous velocity) : Continuous (odePrimitiveExtension trajectory velocity) :=
  continuous_iff_continuousAt.mpr fun time => (odePrimitiveExtension_hasDerivAt trajectory velocity velocityContinuous time).continuousAt

theorem odePrimitiveExtension_initial (trajectory velocity : ℝ → Space) :
    odePrimitiveExtension trajectory velocity 0 = trajectory 0 := by
  simp only [odePrimitiveExtension, intervalIntegral.integral_same, add_zero]

theorem odePrimitiveExtension_eq_on_interior (trajectory velocity : ℝ → Space)
    (velocityContinuous : Continuous velocity) {initialTime finalTime : ℝ}
    (initialNegative : initialTime < 0) (finalPositive : 0 < finalTime)
    (equation : ∀ time ∈ Ioo initialTime finalTime, HasDerivAt trajectory (velocity time) time) :
    EqOn (odePrimitiveExtension trajectory velocity) trajectory (Ioo initialTime finalTime) := by
  intro time inside
  have segmentInside : uIcc (0 : ℝ) time ⊆ Ioo initialTime finalTime := by
    intro current member
    rcases le_total (0 : ℝ) time with nonnegative | nonpositive
    · rw [uIcc_of_le nonnegative] at member
      exact ⟨initialNegative.trans_le member.1, member.2.trans_lt inside.2⟩
    · rw [uIcc_of_ge nonpositive] at member
      exact ⟨inside.1.trans_le member.1, member.2.trans_lt finalPositive⟩
  have integralIdentity := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun current member => equation current (segmentInside member)) (velocityContinuous.intervalIntegrable 0 time)
  rw [odePrimitiveExtension, integralIdentity]
  abel

end EulerNonuniqueness.General
