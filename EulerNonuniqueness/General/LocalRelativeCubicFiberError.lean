import EulerNonuniqueness.General.LocalRelativeCubicError

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace
  cubicCoefficientThirdGroup cubicCoefficientThirdSpace

theorem exists_relative_cubic_fiber_error_ball
    (projection : Space →L[ℝ] Space) (outer : Space → Space →L[ℝ] Space)
    (differential bilinear : Space → BilinearEnd Space) (raw error : Space → Space)
    (outerRegular : LipschitzNear outer (0 : Space))
    (differentialRegular : LipschitzNear differential (0 : Space))
    (bilinearRegular : LipschitzNear bilinear (0 : Space))
    {rawRadius rawConstant normConstant : ℝ}
    (rawRadiusPositive : 0 < rawRadius) (rawNonnegative : 0 ≤ rawConstant) (normNonnegative : 0 ≤ normConstant)
    (rawBound : ∀ initial final : Space,
      initial ∈ ball 0 rawRadius → final ∈ ball 0 rawRadius →
      ‖raw initial - raw final‖ ≤ rawConstant *
        ((‖initial - projection initial‖ + ‖final - projection final‖) ^ 2 *
          ‖(initial - projection initial) - (final - projection final)‖ +
        (‖initial - projection initial‖ + ‖final - projection final‖) ^ 3 * ‖initial - final‖))
    (normBound : ∀ᶠ state in 𝓝 (0 : Space), ‖raw state‖ ≤ normConstant * ‖state - projection state‖ ^ 3)
    (identity : ∀ᶠ state in 𝓝 (0 : Space),
      let relative := state - projection state
      error state = outer state (raw state) -
        outer state (differential state (bilinear state relative relative) relative)) :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      ‖error initial - error final‖ ≤ constant *
        ((‖initial - projection initial‖ + ‖final - projection final‖) ^ 2 *
          ‖(initial - projection initial) - (final - projection final)‖ +
        (‖initial - projection initial‖ + ‖final - projection final‖) ^ 3 * ‖initial - final‖) := by
  let cubic := fun state => cubicFiberCoefficient (ContinuousLinearMap.id ℝ Space)
    (outer state) (differential state) (bilinear state)
  have cubicRegular : LipschitzNear cubic (0 : Space) :=
    lipschitzNear_cubicFiberCoefficient (ContinuousLinearMap.id ℝ Space) outer differential bilinear
      outerRegular differentialRegular bilinearRegular
  have cubicIdentity : ∀ᶠ state in 𝓝 (0 : Space),
      error state = outer state (raw state) -
        cubic state (state - projection state) (state - projection state) (state - projection state) := by
    simpa only [cubic, cubicFiberCoefficient_apply, ContinuousLinearMap.id_apply] using identity
  exact exists_relative_cubic_error_ball projection outer cubic raw error outerRegular cubicRegular
    rawRadiusPositive rawNonnegative normNonnegative rawBound normBound cubicIdentity

end

end EulerNonuniqueness.General
