import EulerNonuniqueness.Section3.ContourCentroidGauge
import EulerNonuniqueness.General.LocalDerivativeLipschitz

noncomputable section

open Set Metric
open scoped BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance centroidGaugeRegularityHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance centroidGaugeRegularityC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance centroidGaugeRegularityDerivativeGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℂ) (σ₁₂ := RingHom.id ℝ)
local instance centroidGaugeRegularityDerivativeSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℂ) (σ₁₂ := RingHom.id ℝ)
local instance centroidGaugeRegularityOperatorGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance centroidGaugeRegularityConstantGroup : NormedAddCommGroup (ℂ →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := ℂ) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem c1ConstantCLM_norm_le_one : ‖c1ConstantCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  simpa only [one_mul] using c1Constant_norm_bound value

theorem contourCentroidGaugeProjection_norm_bound (data : PeriodicC1HolderHalf) :
    ‖contourCentroidGaugeProjection data‖ ≤ 1 + ‖fderiv ℝ contourCentroidFunctional data‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  change ‖contourCentroidGaugeProjection data direction‖ ≤ _
  rw [contourCentroidGaugeProjection_apply]
  have first := norm_sub_le direction (c1Constant ((fderiv ℝ contourCentroidFunctional data) direction))
  have second := (c1Constant_norm_bound ((fderiv ℝ contourCentroidFunctional data) direction)).trans
    ((fderiv ℝ contourCentroidFunctional data).le_opNorm direction)
  calc
    _ ≤ ‖direction‖ + ‖fderiv ℝ contourCentroidFunctional data‖ * ‖direction‖ :=
      first.trans (add_le_add_left second _)
    _ = _ := by ring

theorem contourCentroidGaugeProjection_difference_norm_bound (first second : PeriodicC1HolderHalf) :
    ‖contourCentroidGaugeProjection first - contourCentroidGaugeProjection second‖ ≤
      ‖fderiv ℝ contourCentroidFunctional first - fderiv ℝ contourCentroidFunctional second‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro direction
  change ‖(contourCentroidGaugeProjection first - contourCentroidGaugeProjection second) direction‖ ≤ _
  have identity : (contourCentroidGaugeProjection first - contourCentroidGaugeProjection second) direction =
      c1Constant ((fderiv ℝ contourCentroidFunctional second - fderiv ℝ contourCentroidFunctional first) direction) := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (direction.val.1 label - (fderiv ℝ contourCentroidFunctional first) direction) -
      (direction.val.1 label - (fderiv ℝ contourCentroidFunctional second) direction) = _
    change _ = (fderiv ℝ contourCentroidFunctional second) direction - (fderiv ℝ contourCentroidFunctional first) direction
    ring
  rw [identity]
  apply (c1Constant_norm_bound _).trans
  have actual := (fderiv ℝ contourCentroidFunctional second - fderiv ℝ contourCentroidFunctional first).le_opNorm direction
  simpa only [norm_sub_rev (fderiv ℝ contourCentroidFunctional second) (fderiv ℝ contourCentroidFunctional first)] using actual

theorem contourCentroidGauge_exists_local_uniform_bounds :
    ∃ radius > 0, radius < 1 / 3 ∧ ∃ constant ≥ 0,
      (∀ data ∈ closedBall standardCircleBanach radius, ‖fderiv ℝ contourCentroidFunctional data‖ ≤ constant) ∧
      (∀ first ∈ closedBall standardCircleBanach radius, ∀ second ∈ closedBall standardCircleBanach radius,
        ‖fderiv ℝ contourCentroidFunctional first - fderiv ℝ contourCentroidFunctional second‖ ≤
          constant * ‖first - second‖) ∧
      (∀ data ∈ closedBall standardCircleBanach radius, ‖contourCentroidGaugeProjection data‖ ≤ 1 + constant) ∧
      ∀ first ∈ closedBall standardCircleBanach radius, ∀ second ∈ closedBall standardCircleBanach radius,
        ‖contourCentroidGaugeProjection first - contourCentroidGaugeProjection second‖ ≤
          constant * ‖first - second‖ := by
  have small : ‖standardCircleBanach - standardCircleBanach‖ < (1 / 3 : ℝ) := by
    have identity : standardCircleBanach - standardCircleBanach = 0 := by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      change standardCircleBanach.val.1 label - standardCircleBanach.val.1 label = 0
      ring
    rw [identity]
    change ‖(0 : (ℝ →ᵇ ℂ) × PeriodicHolderHalf)‖ < (1 / 3 : ℝ)
    rw [norm_zero]
    norm_num
  have smooth : ContDiffAt ℝ 2 contourCentroidFunctional standardCircleBanach :=
    (analyticAt_contourCentroidFunctional standardCircleBanach small).contDiffAt
  obtain ⟨radius, positive, constant, nonnegative, bound, difference⟩ :=
    EulerNonuniqueness.General.exists_closedBall_fderiv_bound_of_contDiffAt_two smooth
  let smaller : ℝ := min radius (1 / 6)
  have subset : closedBall standardCircleBanach smaller ⊆ closedBall standardCircleBanach radius :=
    closedBall_subset_closedBall (min_le_left _ _)
  refine ⟨smaller, lt_min positive (by norm_num), (min_le_right _ _).trans_lt (by norm_num),
    constant, nonnegative, (fun data member => bound data (subset member)),
    (fun first firstMember second secondMember => difference first (subset firstMember) second (subset secondMember)), ?_, ?_⟩
  · intro data member
    exact (contourCentroidGaugeProjection_norm_bound data).trans (add_le_add_left (bound data (subset member)) 1)
  · intro first firstMember second secondMember
    exact (contourCentroidGaugeProjection_difference_norm_bound first second).trans
      (difference first (subset firstMember) second (subset secondMember))

end EulerNonuniqueness.Paper
