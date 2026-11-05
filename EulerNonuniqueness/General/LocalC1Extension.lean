import EulerNonuniqueness.General.ODEPrimitiveExtension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Order.ProjIcc

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem exists_global_c1_extension_of_contDiffAt {path : ℝ → Space} {time : ℝ}
    (smooth : ContDiffAt ℝ 1 path time) :
    ∃ extension velocity : ℝ → Space, Continuous extension ∧ Continuous velocity ∧
      (∀ current, HasDerivAt extension (velocity current) current) ∧ extension =ᶠ[𝓝 time] path := by
  obtain ⟨derivative, neighborhood, neighborhoodMember, derivativeContinuous, equation⟩ :=
    contDiffAt_one_iff.mp smooth
  obtain ⟨left, right, timeInside, intervalMember, intervalSubset⟩ :=
    exists_Icc_mem_subset_of_mem_nhds neighborhoodMember
  have ordered : left ≤ right := timeInside.1.trans timeInside.2
  let localVelocity : ℝ → Space := fun current => derivative current 1
  have localContinuous : ContinuousOn localVelocity (Icc left right) :=
    ((ContinuousLinearMap.apply ℝ Space (1 : ℝ)).continuous.comp_continuousOn derivativeContinuous).mono intervalSubset
  let velocity : ℝ → Space := fun current => localVelocity (projIcc left right ordered current)
  have velocityContinuous : Continuous velocity :=
    (continuousOn_iff_continuous_restrict.mp localContinuous).comp continuous_projIcc
  have velocityAgreement : EqOn velocity localVelocity (Icc left right) := by
    intro current member
    simp only [velocity, projIcc_of_mem ordered member]
  let extension : ℝ → Space := fun current => path time + ∫ parameter in time..current, velocity parameter
  have extensionEquation (current : ℝ) : HasDerivAt extension (velocity current) current := by
    exact (intervalIntegral.integral_hasDerivAt_right (velocityContinuous.intervalIntegrable time current)
      velocityContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter velocityContinuous.continuousAt).const_add _
  refine ⟨extension, velocity, continuous_iff_continuousAt.mpr (fun current => (extensionEquation current).continuousAt),
    velocityContinuous, extensionEquation, ?_⟩
  filter_upwards [intervalMember] with current member
  have segmentInside : uIcc time current ⊆ Icc left right :=
    uIcc_subset_Icc timeInside member
  have integralIdentity := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := path)
    (fun parameter parameterMember => by
      have inside := segmentInside parameterMember
      have actual : HasDerivAt path (localVelocity parameter) parameter :=
        (equation parameter (intervalSubset inside)).hasDerivAt
      rw [← velocityAgreement inside] at actual
      exact actual)
    (velocityContinuous.intervalIntegrable time current)
  change path time + ∫ parameter in time..current, velocity parameter = path current
  rw [integralIdentity]
  abel

end EulerNonuniqueness.General
