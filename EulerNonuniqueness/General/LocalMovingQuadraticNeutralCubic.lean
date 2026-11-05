import EulerNonuniqueness.General.MovingQuadraticNeutralCubic
import EulerNonuniqueness.General.LocalFiberOperatorBounds
import EulerNonuniqueness.Section3.LocalLipschitzCalculus

namespace EulerNonuniqueness.General

noncomputable section

open Filter Metric
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace cubicCoefficientThirdGroup cubicCoefficientThirdSpace

theorem exists_relative_moving_neutral_correction_ball
    (neutral : Space →L[ℝ] Space) (transverse velocity : Space → Space)
    (differential : Space → Space →L[ℝ] BilinearEnd Space) (valid : Space → Prop)
    (transverseContinuous : ContinuousAt transverse 0) (transverseZero : transverse 0 = 0)
    (regular : LipschitzNear differential (0 : Space))
    (relative : ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius → valid initial → valid final →
      ‖velocity initial - velocity final‖ ≤ constant *
        ((‖transverse initial‖ + ‖transverse final‖) * ‖transverse initial - transverse final‖ +
          (‖transverse initial‖ + ‖transverse final‖) ^ 2 * ‖neutral initial - neutral final‖))
    (absolute : ∃ constant ≥ 0, ∀ᶠ state in 𝓝 (0 : Space), valid state →
      ‖velocity state‖ ≤ constant * ‖transverse state‖ ^ 2) :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius → valid initial → valid final →
      ‖differential (neutral initial) (velocity initial) (transverse initial) (transverse initial) -
        differential (neutral final) (velocity final) (transverse final) (transverse final)‖ ≤ constant *
        ((‖transverse initial‖ + ‖transverse final‖) ^ 2 * ‖transverse initial - transverse final‖ +
          (‖transverse initial‖ + ‖transverse final‖) ^ 3 * ‖neutral initial - neutral final‖) := by
  obtain ⟨relativeRadius, relativePositive, relativeConstant, relativeNonnegative, relativeBound⟩ := relative
  obtain ⟨absoluteConstant, absoluteNonnegative, absoluteBound⟩ := absolute
  obtain ⟨normBound, normNonnegative, bounded⟩ := exists_eventually_norm_bound
    (Space := Space) (Target := Space →L[ℝ] BilinearEnd Space) regular.continuousAt
  obtain ⟨lip, domain, nearby, lipschitz⟩ := regular
  have neutralLimit : Tendsto neutral (𝓝 (0 : Space)) (𝓝 0) := by
    simpa only [map_zero] using neutral.continuous.tendsto (0 : Space)
  have small : ∀ᶠ state in 𝓝 (0 : Space), ‖transverse state‖ < 1 / 2 :=
    transverseContinuous.norm.eventually (gt_mem_nhds (by
      simp only [transverseZero, norm_zero]; norm_num))
  have combined : {state | state ∈ ball 0 relativeRadius ∧
      (valid state → ‖velocity state‖ ≤ absoluteConstant * ‖transverse state‖ ^ 2) ∧
      ‖differential (neutral state)‖ ≤ normBound ∧ neutral state ∈ domain ∧ ‖transverse state‖ < 1 / 2} ∈ 𝓝 (0 : Space) := by
    filter_upwards [ball_mem_nhds (0 : Space) relativePositive, absoluteBound,
      neutralLimit.eventually bounded, neutralLimit.eventually nearby, small]
      with state inside absolute norm insideDomain size
    exact ⟨inside, absolute, norm, insideDomain, size⟩
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp combined
  let coefficientConstant := normBound + lip
  let velocityConstant := relativeConstant + absoluteConstant
  have coefficientNonnegative : 0 ≤ coefficientConstant := by dsimp only [coefficientConstant]; positivity
  have velocityNonnegative : 0 ≤ velocityConstant := by dsimp only [velocityConstant]; positivity
  refine ⟨radius, positive, 2 * coefficientConstant * velocityConstant, by positivity, ?_⟩
  intro initial final initialInside finalInside initialValid finalValid
  obtain ⟨initialRelative, _, initialNorm, initialDomain, initialSmall⟩ := contained initialInside
  obtain ⟨finalRelative, finalAbsolute, _, finalDomain, finalSmall⟩ := contained finalInside
  have coefficientNorm : ‖differential (neutral initial)‖ ≤ coefficientConstant :=
    initialNorm.trans (le_add_of_nonneg_right lip.coe_nonneg)
  have coefficientDifference : ‖differential (neutral initial) - differential (neutral final)‖ ≤
      coefficientConstant * ‖neutral initial - neutral final‖ :=
    (lipschitz.norm_sub_le (f := differential) initialDomain finalDomain).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left normNonnegative) (norm_nonneg _))
  have velocityDifference := (relativeBound initial final initialRelative finalRelative initialValid finalValid).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right absoluteNonnegative) (by positivity))
  have finalVelocity := (finalAbsolute finalValid).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left relativeNonnegative) (sq_nonneg _))
  exact moving_quadratic_neutral_correction_relative_cubic _ _ _ _ _ _
    coefficientNonnegative velocityNonnegative (norm_nonneg _) (by linarith)
    coefficientNorm coefficientDifference velocityDifference finalVelocity

end

end EulerNonuniqueness.General
