import EulerNonuniqueness.Section3.ContourVelocityCubicTaylor
import EulerNonuniqueness.Section3.ContourVelocityValueBilinear

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def contourVelocityBilinear (data first second : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) : PeriodicC1HolderHalf :=
  (1 / 2 : ℝ) • (contourVelocityQuadratic data (first + second) small -
    contourVelocityQuadratic data first small - contourVelocityQuadratic data second small)

theorem contourVelocityBilinear_value (data first second : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (label : ℝ) :
    (contourVelocityBilinear data first second small).val.1 label =
      (contourVelocityHolderBilinear data first second).val.1 label :=
  congrArg (fun density : PeriodicHolderHalf => density.val.1 label)
    (contourVelocityHolderBilinear_polarization data first second small)

theorem contourVelocityBilinear_diagonal (data increment : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourVelocityBilinear data increment increment small = contourVelocityQuadratic data increment small := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [contourVelocityBilinear_value, contourVelocityHolderBilinear_diagonal]
  rfl

theorem contourVelocityBilinear_add_left (data first second third : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourVelocityBilinear data (first + second) third small =
      contourVelocityBilinear data first third small + contourVelocityBilinear data second third small := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (contourVelocityBilinear data (first + second) third small).val.1 label =
    (contourVelocityBilinear data first third small).val.1 label +
      (contourVelocityBilinear data second third small).val.1 label
  rw [contourVelocityBilinear_value, contourVelocityBilinear_value, contourVelocityBilinear_value]
  exact congrArg (fun density : PeriodicHolderHalf => density.val.1 label)
    (contourVelocityHolderBilinear_add_left data first second third small)

theorem contourVelocityBilinear_real_smul_left (data first second : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℝ) :
    contourVelocityBilinear data (scalar • first) second small =
      scalar • contourVelocityBilinear data first second small := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (contourVelocityBilinear data (scalar • first) second small).val.1 label =
    (scalar : ℂ) * (contourVelocityBilinear data first second small).val.1 label
  rw [contourVelocityBilinear_value, contourVelocityBilinear_value]
  exact congrArg (fun density : PeriodicHolderHalf => density.val.1 label)
    (contourVelocityHolderBilinear_real_smul_left data first second small scalar)

theorem contourVelocityBilinear_symm (data first second : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourVelocityBilinear data first second small = contourVelocityBilinear data second first small := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [contourVelocityBilinear_value, contourVelocityBilinear_value,
    contourVelocityHolderBilinear_symm data first second small]

theorem contourVelocityBilinear_add_right (data first second third : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourVelocityBilinear data first (second + third) small =
      contourVelocityBilinear data first second small + contourVelocityBilinear data first third small := by
  rw [contourVelocityBilinear_symm data first (second + third) small,
    contourVelocityBilinear_add_left data second third first small,
    contourVelocityBilinear_symm data second first small, contourVelocityBilinear_symm data third first small]

theorem contourVelocityBilinear_real_smul_right (data first second : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℝ) :
    contourVelocityBilinear data first (scalar • second) small =
      scalar • contourVelocityBilinear data first second small := by
  rw [contourVelocityBilinear_symm data first (scalar • second) small,
    contourVelocityBilinear_real_smul_left data second first small,
    contourVelocityBilinear_symm data second first small]

end

end EulerNonuniqueness.Paper
