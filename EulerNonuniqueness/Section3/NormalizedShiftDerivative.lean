import EulerNonuniqueness.Section3.NormalizedShiftVelocity
import EulerNonuniqueness.Section3.ContourVelocityQuadraticDerivative
import EulerNonuniqueness.General.OperatorFieldEquivariance

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter Metric
open scoped Topology

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule

theorem contourVelocity_derivative_normalized_shift (data : PeriodicC1HolderHalf) (offset : ℝ)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    (fderiv ℝ extendedContourVelocity (normalizedContourShift offset data)).comp (normalizedContourShiftCLM offset) =
      (normalizedContourShiftCLM offset).comp (fderiv ℝ extendedContourVelocity data) := by
  have shiftedSmall : ‖normalizedContourShift offset data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    rw [normalizedContourShift_distance_circle]
    exact small
  have equivariant : (fun current => extendedContourVelocity (normalizedContourShiftCLM offset current)) =ᶠ[𝓝 data]
      (fun current => normalizedContourShiftCLM offset (extendedContourVelocity current)) := by
    have neighborhood : ball standardCircleBanach (min 1 (2 / (3 * Real.pi))) ∈ 𝓝 data := isOpen_ball.mem_nhds (by
      simpa only [mem_ball, dist_eq_norm data standardCircleBanach] using small)
    filter_upwards [neighborhood] with current member
    exact extendedContourVelocity_normalized_shift current offset
      (by simpa only [mem_ball, dist_eq_norm current standardCircleBanach] using member)
  have transformed : DifferentiableAt ℝ extendedContourVelocity (normalizedContourShiftCLM offset data) := by
    rw [normalizedContourShiftCLM_apply]
    exact differentiableAt_extendedContourVelocity (normalizedContourShift offset data) shiftedSmall
  have result : (fderiv ℝ extendedContourVelocity (normalizedContourShiftCLM offset data)).comp (normalizedContourShiftCLM offset) =
      (normalizedContourShiftCLM offset).comp (fderiv ℝ extendedContourVelocity data) := by
    with_reducible
      exact EulerNonuniqueness.General.fderiv_intertwines_of_equivariant (Space := PeriodicC1HolderHalf) extendedContourVelocity
        (normalizedContourShiftCLM offset) data (differentiableAt_extendedContourVelocity data small)
        transformed equivariant
  simpa only [normalizedContourShiftCLM_apply] using result

theorem contourVelocity_second_derivative_normalized_shift (offset : ℝ)
    (first second : PeriodicC1HolderHalf) :
    fderiv ℝ (fun current : PeriodicC1HolderHalf => fderiv ℝ extendedContourVelocity current) standardCircleBanach
      (normalizedContourShift offset first) (normalizedContourShift offset second) =
    normalizedContourShift offset
      (fderiv ℝ (fun current : PeriodicC1HolderHalf => fderiv ℝ extendedContourVelocity current) standardCircleBanach first second) := by
  have positive : (0 : ℝ) < min 1 (2 / (3 * Real.pi)) := by positivity
  have derivative : HasFDerivAt (fun current : PeriodicC1HolderHalf => fderiv ℝ extendedContourVelocity current)
      (fderiv ℝ (fun current : PeriodicC1HolderHalf => fderiv ℝ extendedContourVelocity current) standardCircleBanach) standardCircleBanach := by
    with_reducible
      exact DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
        (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
        (differentiableAt_fderiv_extendedContourVelocity standardCircleBanach (by simpa using positive))
  have equivariant : (fun current => (fderiv ℝ extendedContourVelocity (normalizedContourShiftCLM offset current)).comp
      (normalizedContourShiftCLM offset)) =ᶠ[𝓝 standardCircleBanach]
      (fun current => (normalizedContourShiftCLM offset).comp (fderiv ℝ extendedContourVelocity current)) := by
    filter_upwards [ball_mem_nhds standardCircleBanach positive] with current member
    exact contourVelocity_derivative_normalized_shift current offset
      (by simpa only [mem_ball, dist_eq_norm current standardCircleBanach] using member)
  have result : (fderiv ℝ (fun current : PeriodicC1HolderHalf => fderiv ℝ extendedContourVelocity current) standardCircleBanach)
      (normalizedContourShiftCLM offset first) (normalizedContourShiftCLM offset second) =
      normalizedContourShiftCLM offset
        ((fderiv ℝ (fun current : PeriodicC1HolderHalf => fderiv ℝ extendedContourVelocity current) standardCircleBanach) first second) := by
    let field : PeriodicC1HolderHalf → PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
      fun current => fderiv ℝ extendedContourVelocity current
    let secondOperator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
      fderiv ℝ field standardCircleBanach
    with_reducible
      exact EulerNonuniqueness.General.derivative_operator_field_intertwines
        (Space := PeriodicC1HolderHalf) field (normalizedContourShiftCLM offset)
        standardCircleBanach secondOperator
        (normalizedContourShift_circle offset) derivative equivariant first second
  simpa only [normalizedContourShiftCLM_apply] using result

theorem contourVelocity_quadratic_normalized_shift (offset : ℝ) (first second : PeriodicC1HolderHalf) :
    contourVelocityQuadraticDerivativeCLM standardCircleBanach
      (normalizedContourShift offset first) (normalizedContourShift offset second) =
      normalizedContourShift offset (contourVelocityQuadraticDerivativeCLM standardCircleBanach first second) := by
  change (1 / 2 : ℝ) • (fderiv ℝ (fun current : PeriodicC1HolderHalf => fderiv ℝ extendedContourVelocity current) standardCircleBanach
    (normalizedContourShift offset first) (normalizedContourShift offset second)) =
    normalizedContourShiftCLM offset ((1 / 2 : ℝ) •
      (fderiv ℝ (fun current : PeriodicC1HolderHalf => fderiv ℝ extendedContourVelocity current) standardCircleBanach first second))
  rw [contourVelocity_second_derivative_normalized_shift]
  exact ((normalizedContourShiftCLM offset).map_smul (1 / 2 : ℝ) _).symm

end

end EulerNonuniqueness.Paper
