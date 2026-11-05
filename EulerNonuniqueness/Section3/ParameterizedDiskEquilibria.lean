import EulerNonuniqueness.Section3.NearCircleBoundaryBiotSavart

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem nearCircleInterior_eq_unitBall_of_unit_norm (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (unit_norm : ∀ label, ‖data.val.1 label‖ = 1) :
    nearCircleInterior data small = Metric.ball (0 : ℂ) 1 := by
  have profile_identity : nearCircleRadialProfile data small = fun _ => (1 : ℝ) := by
    funext angle
    exact unit_norm _
  ext position
  change ‖position‖ < nearCircleRadialProfile data small (Complex.arg position) ↔ dist position 0 < 1
  rw [profile_identity, dist_zero_right]

theorem integral_unitBall_biotSavart_boundary (position : ℂ) (unit_norm : ‖position‖ = 1) :
    (∫ source in Metric.ball (0 : ℂ) 1, biotSavartKernel (position - source)) = (Complex.I / 2) * position := by
  have small : ‖standardCircleBanach - standardCircleBanach‖ < 1 / 3 := by norm_num
  have chord_small : ‖standardCircleBanach - standardCircleBanach‖ < 2 / (3 * Real.pi) := by
    have zero : ‖standardCircleBanach - standardCircleBanach‖ = 0 := by norm_num
    rw [zero]
    positivity
  have position_identity : standardCircle (Complex.arg position) = position := by
    simpa only [unit_norm, Complex.ofReal_one, one_mul, standardCircle] using Complex.norm_mul_exp_arg_mul_I position
  have identity := integral_nearCircleInterior_biotSavart_boundary standardCircleBanach small chord_small (Complex.arg position)
  rw [nearCircleInterior_standardCircle small, periodicContourVelocity_centered] at identity
  change (∫ source in Metric.ball (0 : ℂ) 1, biotSavartKernel (standardCircle (Complex.arg position) - source)) =
    contourVelocity standardCircle standardCircleTangent (Complex.arg position)
      (Complex.arg position - Real.pi) (Complex.arg position + Real.pi) at identity
  rw [standardCircle_contourVelocity_at, position_identity] at identity
  exact identity

theorem contourVelocity_eq_disk_rotation_of_unit_norm (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (chord_small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi))
    (unit_norm : ∀ label, ‖data.val.1 label‖ = 1) (target : ℝ) :
    contourVelocity data.val.1 data.val.2.val.1 target (-Real.pi) Real.pi =
      (Complex.I / 2) * data.val.1 target := by
  rw [← integral_nearCircleInterior_biotSavart_boundary data small chord_small,
    nearCircleInterior_eq_unitBall_of_unit_norm data small unit_norm]
  exact integral_unitBall_biotSavart_boundary _ (unit_norm target)

theorem parameterizedDisk_rotatingFrame_stationary (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (chord_small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi))
    (unit_norm : ∀ label, ‖data.val.1 label‖ = 1) (target : ℝ) :
    contourVelocity data.val.1 data.val.2.val.1 target (-Real.pi) Real.pi -
      (Complex.I / 2) * data.val.1 target = 0 := by
  rw [contourVelocity_eq_disk_rotation_of_unit_norm data small chord_small unit_norm, sub_self]

end

end EulerNonuniqueness.Paper
