import EulerNonuniqueness.General.QuadraticVelocityBilinearCubic
import EulerNonuniqueness.General.LocalFiberOperatorBounds
import EulerNonuniqueness.Section3.LocalLipschitzCalculus

namespace EulerNonuniqueness.General

noncomputable section

open Filter Metric
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace

theorem exists_relative_quadratic_velocity_bilinear_ball
    (neutral : Space →L[ℝ] Space) (transverse velocity : Space → Space)
    (coefficient : Space → BilinearEnd Space) (valid : Space → Prop)
    (regular : LipschitzNear coefficient (0 : Space))
    (relative : ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius → valid initial → valid final →
      ‖velocity initial - velocity final‖ ≤ constant *
        ((‖transverse initial‖ + ‖transverse final‖) * ‖transverse initial - transverse final‖ +
          (‖transverse initial‖ + ‖transverse final‖) ^ 2 * ‖neutral initial - neutral final‖))
    (absolute : ∃ constant ≥ 0, ∀ᶠ state in 𝓝 (0 : Space), valid state →
      ‖velocity state‖ ≤ constant * ‖transverse state‖ ^ 2) :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius → valid initial → valid final →
      ‖coefficient (neutral initial) (velocity initial) (transverse initial) -
        coefficient (neutral final) (velocity final) (transverse final)‖ ≤ constant *
        ((‖transverse initial‖ + ‖transverse final‖) ^ 2 * ‖transverse initial - transverse final‖ +
          (‖transverse initial‖ + ‖transverse final‖) ^ 3 * ‖neutral initial - neutral final‖) := by
  obtain ⟨relativeRadius, relativePositive, relativeConstant, relativeNonnegative, relativeBound⟩ := relative
  obtain ⟨absoluteConstant, absoluteNonnegative, absoluteBound⟩ := absolute
  obtain ⟨normBound, normNonnegative, bounded⟩ := exists_eventually_norm_bound
    (Space := Space) (Target := BilinearEnd Space) regular.continuousAt
  obtain ⟨lip, domain, nearby, lipschitz⟩ := regular
  have neutralLimit : Tendsto neutral (𝓝 (0 : Space)) (𝓝 0) := by
    simpa only [map_zero] using neutral.continuous.tendsto (0 : Space)
  have combined : {state | state ∈ ball 0 relativeRadius ∧
      (valid state → ‖velocity state‖ ≤ absoluteConstant * ‖transverse state‖ ^ 2) ∧
      ‖coefficient (neutral state)‖ ≤ normBound ∧ neutral state ∈ domain} ∈ 𝓝 (0 : Space) := by
    filter_upwards [ball_mem_nhds (0 : Space) relativePositive, absoluteBound,
      neutralLimit.eventually bounded, neutralLimit.eventually nearby]
      with state inside absolute norm insideDomain
    exact ⟨inside, absolute, norm, insideDomain⟩
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp combined
  let coefficientConstant := normBound + lip
  let velocityConstant := relativeConstant + absoluteConstant
  have coefficientNonnegative : 0 ≤ coefficientConstant := by dsimp only [coefficientConstant]; positivity
  have velocityNonnegative : 0 ≤ velocityConstant := by dsimp only [velocityConstant]; positivity
  refine ⟨radius, positive, 2 * coefficientConstant * velocityConstant, by positivity, ?_⟩
  intro initial final initialInside finalInside initialValid finalValid
  obtain ⟨initialRelative, _, initialNorm, initialDomain⟩ := contained initialInside
  obtain ⟨finalRelative, finalAbsolute, _, finalDomain⟩ := contained finalInside
  have coefficientNorm : ‖coefficient (neutral initial)‖ ≤ coefficientConstant :=
    initialNorm.trans (le_add_of_nonneg_right lip.coe_nonneg)
  have coefficientDifference : ‖coefficient (neutral initial) - coefficient (neutral final)‖ ≤
      coefficientConstant * ‖neutral initial - neutral final‖ :=
    (lipschitz.norm_sub_le (f := coefficient) initialDomain finalDomain).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left normNonnegative) (norm_nonneg _))
  have velocityDifference := (relativeBound initial final initialRelative finalRelative initialValid finalValid).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right absoluteNonnegative) (by positivity))
  have finalVelocity := (finalAbsolute finalValid).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left relativeNonnegative) (sq_nonneg _))
  exact quadratic_velocity_bilinear_relative_cubic _ _ _ _ _ _
    coefficientNonnegative velocityNonnegative (norm_nonneg _)
    coefficientNorm coefficientDifference velocityDifference finalVelocity

end

end EulerNonuniqueness.General
