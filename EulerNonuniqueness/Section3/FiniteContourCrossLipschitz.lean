import EulerNonuniqueness.Section3.FiniteContourGeometry
import EulerNonuniqueness.Section3.ExtendedCrossContour

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def FiniteContourConfiguration.crossLipschitzCoefficient {count : ℕ}
    (configuration : FiniteContourConfiguration count) (first second : Fin count) : ℝ :=
  (crossContourIntegrandLipschitzBound (configuration.crossNormBound first second)
    (configuration.crossGap first second) / 2) * (configuration.radius first + configuration.radius second)

theorem FiniteContourConfiguration.crossNormBound_nonneg {count : ℕ}
    (configuration : FiniteContourConfiguration count) (first second : Fin count) :
    0 ≤ configuration.crossNormBound first second := by
  have : 0 ≤ ‖configuration.center first‖ + 3 * configuration.radius first := by
    have radius_pos := configuration.radius_pos first
    positivity
  exact this.trans (le_max_left _ _)

theorem FiniteContourConfiguration.crossLipschitzCoefficient_nonneg {count : ℕ}
    (configuration : FiniteContourConfiguration count) (first second : Fin count) (distinct : first ≠ second) :
    0 ≤ configuration.crossLipschitzCoefficient first second := by
  have constant_nonneg := crossContourIntegrandLipschitzBound_nonneg
    (configuration.crossNormBound_nonneg first second) (configuration.crossGap_pos first second distinct)
  have first_pos := configuration.radius_pos first
  have second_pos := configuration.radius_pos second
  unfold FiniteContourConfiguration.crossLipschitzCoefficient
  positivity

set_option maxHeartbeats 1000000 in
theorem FiniteContourConfiguration.cross_velocity_parameter_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (first second : Fin count → PeriodicC1HolderHalf)
    (target source : Fin count) (distinct : target ≠ source)
    (first_bounded : ∀ index, ‖first index‖ ≤ 3) (second_bounded : ∀ index, ‖second index‖ ≤ 3) :
    ‖extendedCrossContourVelocity (configuration.physicalContour first target) (configuration.physicalContour first source) -
      extendedCrossContourVelocity (configuration.physicalContour second target) (configuration.physicalContour second source)‖ ≤
      configuration.crossLipschitzCoefficient target source * ‖first - second‖ := by
  have estimate := extendedCrossContourVelocity_parameter_norm_bound
    (configuration.physicalContour first target) (configuration.physicalContour first source)
    (configuration.physicalContour second target) (configuration.physicalContour second source)
    (configuration.crossGap_pos target source distinct)
    (configuration.physicalContour_separated first target source (first_bounded target) (first_bounded source))
    (configuration.physicalContour_separated second target source (second_bounded target) (second_bounded source))
    ((configuration.physicalContour_norm_bound first target (first_bounded target)).trans (le_max_left _ _))
    ((configuration.physicalContour_norm_bound first source (first_bounded source)).trans (le_max_right _ _))
    ((configuration.physicalContour_norm_bound second target (second_bounded target)).trans (le_max_left _ _))
    ((configuration.physicalContour_norm_bound second source (second_bounded source)).trans (le_max_right _ _))
  rw [configuration.physicalContour_parameter_norm first second target,
    configuration.physicalContour_parameter_norm first second source] at estimate
  have target_bound : ‖first target - second target‖ ≤ ‖first - second‖ := norm_le_pi_norm (first - second) target
  have source_bound : ‖first source - second source‖ ≤ ‖first - second‖ := norm_le_pi_norm (first - second) source
  have sum_bound : configuration.radius target * ‖first target - second target‖ +
      configuration.radius source * ‖first source - second source‖ ≤
      (configuration.radius target + configuration.radius source) * ‖first - second‖ := by
    have target_scaled := mul_le_mul_of_nonneg_left target_bound (configuration.radius_pos target).le
    have source_scaled := mul_le_mul_of_nonneg_left source_bound (configuration.radius_pos source).le
    nlinarith
  have constant_nonneg := crossContourIntegrandLipschitzBound_nonneg
    (configuration.crossNormBound_nonneg target source) (configuration.crossGap_pos target source distinct)
  apply estimate.trans
  exact (mul_le_mul_of_nonneg_left sum_bound (div_nonneg constant_nonneg (by norm_num))).trans_eq (by
    unfold FiniteContourConfiguration.crossLipschitzCoefficient
    ring)

end

end EulerNonuniqueness.Paper
