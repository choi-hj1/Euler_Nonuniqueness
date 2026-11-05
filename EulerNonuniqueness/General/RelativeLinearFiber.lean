import EulerNonuniqueness.General.CoordinatizedIncrementDifference
import EulerNonuniqueness.General.LocalLipschitzBallBounds

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def coordinatizedFiberDefect (function : Space → Space) (projection : Space →L[ℝ] Space)
    (coordinates : Space → Space →L[ℝ] Space) (state : Space) : Space :=
  function (projection state + coordinates (projection state) (state - projection state)) - function (projection state)

theorem exists_relative_linear_fiber_ball (function : Space → Space)
    (projection : Space →L[ℝ] Space) (coordinates : Space → Space →L[ℝ] Space)
    (functionRegular : HasLipschitzDerivativeNear function (0 : Space))
    (coordinateRegular : LipschitzNear coordinates (0 : Space)) :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      ‖coordinatizedFiberDefect function projection coordinates initial -
        coordinatizedFiberDefect function projection coordinates final‖ ≤ constant *
        (‖(initial - projection initial) - (final - projection final)‖ +
          ‖projection initial - projection final‖ * ‖final - projection final‖) := by

  obtain ⟨rawRadius, rawPositive, rawConstant, rawNonnegative, raw⟩ :=
    EulerNonuniqueness.General.exists_relative_linear_increment_ball function functionRegular
  obtain ⟨coordinateRadius, coordinatePositive, bound, boundOne, bounded, coefficientDifference⟩ :=
    coordinateRegular.exists_closedBall_bounds
  let relative : Space →L[ℝ] Space :=
    ContinuousLinearMap.id ℝ Space - projection
  have neutralContinuous : ContinuousAt (fun state => ‖projection state‖)
      (0 : Space) := projection.continuous.continuousAt.norm
  have neutralSmall : ∀ᶠ state in 𝓝 (0 : Space),
      ‖projection state‖ < coordinateRadius :=
    neutralContinuous.eventually (gt_mem_nhds (by simpa only [map_zero, norm_zero] using coordinatePositive))
  have sizeContinuous : ContinuousAt (fun state => ‖projection state‖ + bound * ‖relative state‖)
      (0 : Space) :=
    neutralContinuous.add (continuousAt_const.mul relative.continuous.continuousAt.norm)
  have sizeSmall : ∀ᶠ state in 𝓝 (0 : Space),
      ‖projection state‖ + bound * ‖relative state‖ < rawRadius / 4 :=
    sizeContinuous.eventually (gt_mem_nhds (by simpa only [map_zero, norm_zero, mul_zero, zero_add] using
      (show 0 < rawRadius / 4 by positivity)))
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp (neutralSmall.and sizeSmall)
  refine ⟨radius, positive, 2 * rawConstant * bound, by positivity, ?_⟩
  intro initial final initialInside finalInside
  obtain ⟨initialNeutralSmall, initialSize⟩ := contained initialInside
  obtain ⟨finalNeutralSmall, finalSize⟩ := contained finalInside
  have firstBound := bounded (projection initial) initialNeutralSmall.le
  have secondBound := bounded (projection final) finalNeutralSmall.le
  have difference := coefficientDifference (projection initial) (projection final)
    initialNeutralSmall.le finalNeutralSmall.le
  have imageBound (state : Space)
      (boundState : ‖coordinates (projection state)‖ ≤ bound) :
      ‖coordinates (projection state) (relative state)‖ ≤ bound * ‖relative state‖ :=
    ((coordinates (projection state)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right boundState (norm_nonneg _))
  have firstImage := imageBound initial firstBound
  have secondImage := imageBound final secondBound
  have boundNonnegative : 0 ≤ bound := by linarith
  have firstDomain : ‖projection initial‖ +
      (‖coordinates (projection initial) (relative initial)‖ +
        ‖coordinates (projection final) (relative final)‖) ≤ rawRadius := by
    linarith [norm_nonneg (projection final)]
  have finalDomain : ‖projection final‖ +
      (‖coordinates (projection initial) (relative initial)‖ +
        ‖coordinates (projection final) (relative final)‖) ≤ rawRadius := by
    linarith [norm_nonneg (projection initial)]
  have rawBound := raw (projection initial) (projection final)
    (coordinates (projection initial) (relative initial))
    (coordinates (projection final) (relative final)) firstDomain finalDomain
  have actual := EulerNonuniqueness.General.coordinatized_increment_difference_norm_le
    function (projection initial) (projection final)
    (relative initial) (relative final)
    (coordinates (projection initial))
    (coordinates (projection final))
    rawNonnegative boundNonnegative firstBound secondBound difference rawBound
  exact actual
end EulerNonuniqueness.General
