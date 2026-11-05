import EulerNonuniqueness.Section3.ContourCentroidGaugeRegularity
import EulerNonuniqueness.General.ConstraintTangentQuadratic

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance centroidTangentC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph
local instance centroidTangentC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem contourCentroidGaugeProjection_exists_uniform_quadratic_deviation :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ data direction : PeriodicC1HolderHalf,
      ‖data - standardCircleBanach‖ + ‖direction‖ ≤ radius →
      contourCentroidFunctional (data + direction) = contourCentroidFunctional data →
      ‖contourCentroidGaugeProjection data direction - direction‖ ≤ constant * ‖direction‖ ^ 2 := by
  let shifted : PeriodicC1HolderHalf → ℂ := fun increment => contourCentroidFunctional (standardCircleBanach + increment)
  have atCircle : AnalyticAt ℝ contourCentroidFunctional standardCircleBanach :=
    analyticAt_contourCentroidFunctional _ (by simpa only [sub_self, norm_zero] using (by norm_num : (0 : ℝ) < 1 / 3))
  have translation : AnalyticAt ℝ (fun increment : PeriodicC1HolderHalf => standardCircleBanach + increment) 0 :=
    analyticAt_const.add analyticAt_id
  have shiftedAnalytic : AnalyticAt ℝ shifted 0 := by
    exact AnalyticAt.comp_of_eq (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      (G := ℂ) atCircle translation (by simp)
  have regular := EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt shiftedAnalytic
  obtain ⟨radius, positive, constant, nonnegative, tangent⟩ := regular.exists_constraint_tangent_quadratic shifted
  refine ⟨min radius (1 / 6), lt_min positive (by norm_num), constant, nonnegative, ?_⟩
  intro data direction inside sameValue
  have small : ‖data - standardCircleBanach‖ < 1 / 3 := by
    have actual := inside.trans (min_le_right _ _)
    linarith [norm_nonneg direction]
  have actualDerivative : HasFDerivAt shifted (fderiv ℝ contourCentroidFunctional data) (data - standardCircleBanach) := by
    have translate : HasFDerivAt (fun increment : PeriodicC1HolderHalf => standardCircleBanach + increment)
        (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf) (data - standardCircleBanach) :=
      (hasFDerivAt_id (𝕜 := ℝ) _).const_add standardCircleBanach
    have outer := (analyticAt_contourCentroidFunctional data small).differentiableAt.hasFDerivAt
    have identity : standardCircleBanach + (data - standardCircleBanach) = data := by abel
    rw [← identity] at outer
    have composite := HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      (G := ℂ) (data - standardCircleBanach) outer translate
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, identity] using composite
  have constraint : shifted ((data - standardCircleBanach) + direction) = shifted (data - standardCircleBanach) := by
    have identity : standardCircleBanach + (data - standardCircleBanach) = data := by abel
    simpa only [shifted, ← add_assoc, identity] using sameValue
  have bound := tangent (data - standardCircleBanach) direction (inside.trans (min_le_left _ _)) constraint
  rw [actualDerivative.fderiv] at bound
  have identity : contourCentroidGaugeProjection data direction - direction =
      -c1Constant ((fderiv ℝ contourCentroidFunctional data) direction) := by
    rw [contourCentroidGaugeProjection_apply]
    abel
  rw [identity, norm_neg]
  exact (c1Constant_norm_bound _).trans bound

end EulerNonuniqueness.Paper
