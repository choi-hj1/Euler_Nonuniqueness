import EulerNonuniqueness.Section3.ContourVelocityUniformCubicTaylor

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance] secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule

def contourVelocityQuadraticDerivativeCLM (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  @SMul.smul ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
    (inferInstance : SMul ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf))
    (1 / 2) (fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) data)

theorem contourVelocityQuadraticDerivativeCLM_eq (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius) :
    contourVelocityQuadraticDerivativeCLM data = contourVelocityBilinearCLM data nonnegative gap small nearby := by
  unfold contourVelocityQuadraticDerivativeCLM
  rw [fderiv_fderiv_extendedContourVelocity_eq data nonnegative gap small nearby]
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  change (1 / 2 : ℝ) • ((2 : ℝ) • contourVelocityBilinearCLM data nonnegative gap small nearby first second) = _
  rw [smul_smul]
  norm_num

theorem contourVelocityQuadraticDerivativeCLM_symm (data first second : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius) :
    contourVelocityQuadraticDerivativeCLM data first second = contourVelocityQuadraticDerivativeCLM data second first := by
  rw [contourVelocityQuadraticDerivativeCLM_eq data nonnegative gap small nearby]
  exact contourVelocityBilinearCLM_symm data first second nonnegative gap small nearby

theorem contourVelocity_actual_uniform_cubic_taylor_bound (data increment : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius)
    (incrementSmall : ‖increment‖ ≤ (outerRadius - innerRadius) / 4)
    (inverseSmall : ‖increment‖ ≤ (1 - outerRadius) / 2) (incrementBound : ‖increment‖ ≤ 1) :
    ‖extendedContourVelocity (data + increment) - extendedContourVelocity data -
      fderiv ℝ extendedContourVelocity data increment -
      contourVelocityQuadraticDerivativeCLM data increment increment‖ ≤
      contourVelocityUniformCubicBound innerRadius outerRadius * ‖increment‖ ^ 3 := by
  rw [contourVelocityQuadraticDerivativeCLM_eq data nonnegative gap small nearby]
  exact contourVelocity_uniform_cubic_taylor_bound data increment nonnegative gap small nearby
    incrementSmall inverseSmall incrementBound

end

end EulerNonuniqueness.Paper
