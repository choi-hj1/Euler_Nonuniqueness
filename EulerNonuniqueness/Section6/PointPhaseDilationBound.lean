import EulerNonuniqueness.Section6.ForcedPointImpulse
import EulerNonuniqueness.Section6.PointPhaseVelocity

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

theorem point_dilation_forcing_rate_bound {positive negative : ℂ} {forcing : ℂ × ℂ} {length budget : ℝ}
    (lengthPositive : 0 < length) (positiveNonzero : positive ≠ 0)
    (negativeSmall : ‖negative‖ ≤ ‖positive‖ / 2)
    (differenceUpper : ‖positive‖ ^ 2 - ‖negative‖ ^ 2 ≤ 2 * length ^ 2)
    (budgetNonnegative : 0 ≤ budget) (forcingBound : ‖forcing‖ / ‖positive‖ ≤ budget) :
    |(2 * @inner ℝ ℂ _ positive forcing.1 - 2 * @inner ℝ ℂ _ negative forcing.2) / length ^ 2| ≤ 12 * budget := by
  have positiveNorm : 0 < ‖positive‖ := norm_pos_iff.mpr positiveNonzero
  have negativeSquare : ‖negative‖ ^ 2 ≤ (‖positive‖ / 2) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr negativeSmall
  have positiveSquare : ‖positive‖ ^ 2 ≤ 3 * length ^ 2 := by nlinarith
  have negativeWeaker : ‖negative‖ ≤ ‖positive‖ := by linarith [norm_nonneg positive]
  have normForcing : ‖forcing‖ ≤ budget * ‖positive‖ := (div_le_iff₀ positiveNorm).mp forcingBound
  have estimate := forced_point_impulse_rate_bound positive negative forcing.1 forcing.2
  have numerator : |2 * @inner ℝ ℂ _ positive forcing.1 - 2 * @inner ℝ ℂ _ negative forcing.2| ≤
      12 * budget * length ^ 2 := by
    calc
      _ ≤ 2 * (‖positive‖ + ‖negative‖) * ‖forcing‖ := estimate
      _ ≤ 2 * (‖positive‖ + ‖positive‖) * (budget * ‖positive‖) := by gcongr
      _ = 4 * budget * ‖positive‖ ^ 2 := by ring
      _ ≤ 4 * budget * (3 * length ^ 2) := mul_le_mul_of_nonneg_left positiveSquare (by positivity)
      _ = _ := by ring
  rw [abs_div, abs_of_pos (sq_pos_of_pos lengthPositive)]
  exact (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mpr numerator

theorem exists_uniform_forced_point_phase_error_bound :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ, ∀ positive negative : ℂ,
      ∀ forcing : ℂ × ℂ, 0 ≤ coefficient → positive ≠ 0 → negative ≠ 0 →
      star positive ^ 2 - star negative ^ 2 ≠ 0 → ‖negative‖ < ‖positive‖ →
      ‖pointShapeChart positive negative‖ < radius →
      |((positivePointVelocity coefficient positive negative + forcing.1) / positive).im +
          coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2)| ≤
        bound * (coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2)) * ‖pointShapeChart positive negative‖ +
          ‖forcing‖ / ‖positive‖ := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ := exists_uniform_point_rotation_error_bound
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient positive negative forcing coefficientNonnegative positiveNonzero negativeNonzero squaresNonzero normOrder small
  have differencePositive : 0 < ‖positive‖ ^ 2 - ‖negative‖ ^ 2 := by
    nlinarith [norm_nonneg negative, norm_nonneg positive]
  have frequencyNonnegative : 0 ≤ coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2) :=
    div_nonneg coefficientNonnegative differencePositive.le
  have reconstruction := shapeChart_reconstruction (pointShapeRatio positive negative) (pointShapeAngle positive negative)
  have rotationEstimate := estimate (coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2))
    (pointShapeChart positive negative) small
  rw [abs_of_nonneg frequencyNonnegative] at rotationEstimate
  have ratioIdentity : shapeChartRatio (pointShapeChart positive negative) = pointShapeRatio positive negative := reconstruction.1
  have phaseIdentity : shapeChartAngle (pointShapeChart positive negative) = pointShapeAngle positive negative := reconstruction.2
  rw [ratioIdentity, phaseIdentity] at rotationEstimate
  rw [add_div, Complex.add_im, positive_point_log_im_eq_rotation coefficient positiveNonzero negativeNonzero squaresNonzero normOrder]
  calc
    _ = |(rotationVelocity (coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2))
        (pointShapeRatio positive negative) (pointShapeAngle positive negative) +
        coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2)) + (forcing.1 / positive).im| := by ring_nf
    _ ≤ |rotationVelocity (coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2))
        (pointShapeRatio positive negative) (pointShapeAngle positive negative) +
        coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2)| + |(forcing.1 / positive).im| := abs_add_le _ _
    _ ≤ bound * (coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2)) * ‖pointShapeChart positive negative‖ +
        ‖forcing‖ / ‖positive‖ := add_le_add rotationEstimate
      ((Complex.abs_im_le_norm _).trans (by rw [norm_div]; exact div_le_div_of_nonneg_right (norm_fst_le forcing) (norm_nonneg _)))

end EulerNonuniqueness.Section6
