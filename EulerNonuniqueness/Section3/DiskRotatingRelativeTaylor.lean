import EulerNonuniqueness.Section3.DiskRotatingThirdRegularity
import EulerNonuniqueness.General.RelativeQuadraticTaylorUniform

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace

local instance rotatingRelativeC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskRotatingOffset (increment : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskEulerRotatingField (standardCircleBanach + increment)

def diskRotatingDerivativeOffset (increment : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  fderiv ℝ diskEulerRotatingField (standardCircleBanach + increment)

theorem diskEulerRotatingField_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      diskEulerRotatingField standardCircleBanach := by
  have second := diskEulerRotatingField_derivative_hasLipschitzDerivativeNear
  refine ⟨⟨?_, second.lipschitzNear⟩, second⟩
  have threshold : (0 : ℝ) < min 1 (2 / (3 * Real.pi)) := by positivity
  filter_upwards [ball_mem_nhds standardCircleBanach threshold] with data member
  exact differentiableAt_diskEulerRotatingField data
    (by simpa only [mem_ball, dist_eq_norm data standardCircleBanach] using member)

theorem diskRotatingOffset_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      diskRotatingOffset (0 : PeriodicC1HolderHalf) := by
  have translation := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_of_analyticAt
    (show AnalyticAt ℝ (fun increment : PeriodicC1HolderHalf => standardCircleBanach + increment) 0 from
      analyticAt_const.add analyticAt_id)
  have outer : EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear diskEulerRotatingField
      (standardCircleBanach + (0 : PeriodicC1HolderHalf)) := by
    simpa only [add_zero] using diskEulerRotatingField_hasLipschitzSecondDerivativeNear
  exact outer.comp translation

theorem diskRotatingDerivativeOffset_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      diskRotatingDerivativeOffset (0 : PeriodicC1HolderHalf) := by
  have translation := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_of_analyticAt
    (show AnalyticAt ℝ (fun increment : PeriodicC1HolderHalf => standardCircleBanach + increment) 0 from
      analyticAt_const.add analyticAt_id)
  have outer : EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      (fderiv ℝ diskEulerRotatingField) (standardCircleBanach + (0 : PeriodicC1HolderHalf)) := by
    simpa only [add_zero] using diskEulerRotatingField_derivative_hasLipschitzSecondDerivativeNear
  exact outer.comp translation

theorem diskRotatingOffset_exists_relative_quadratic_taylor_ball :
    ∃ radius > 0, ∃ constant : NNReal, ∀ initialBase finalBase initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖initialBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖finalBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖(diskRotatingOffset (initialBase + initialIncrement) - diskRotatingOffset initialBase -
          fderiv ℝ diskRotatingOffset initialBase initialIncrement) -
        (diskRotatingOffset (finalBase + finalIncrement) - diskRotatingOffset finalBase -
          fderiv ℝ diskRotatingOffset finalBase finalIncrement)‖ ≤ (constant : ℝ) *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 2) := by
  exact EulerNonuniqueness.General.exists_relative_quadratic_taylor_ball diskRotatingOffset
    diskRotatingOffset_hasLipschitzSecondDerivativeNear

theorem diskRotatingDerivativeOffset_exists_relative_quadratic_taylor_ball :
    ∃ radius > 0, ∃ constant : NNReal, ∀ initialBase finalBase initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖initialBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖finalBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖(diskRotatingDerivativeOffset (initialBase + initialIncrement) - diskRotatingDerivativeOffset initialBase -
          fderiv ℝ diskRotatingDerivativeOffset initialBase initialIncrement) -
        (diskRotatingDerivativeOffset (finalBase + finalIncrement) - diskRotatingDerivativeOffset finalBase -
          fderiv ℝ diskRotatingDerivativeOffset finalBase finalIncrement)‖ ≤ (constant : ℝ) *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 2) := by
  exact EulerNonuniqueness.General.exists_relative_quadratic_taylor_ball diskRotatingDerivativeOffset
    diskRotatingDerivativeOffset_hasLipschitzSecondDerivativeNear

end EulerNonuniqueness.Paper
