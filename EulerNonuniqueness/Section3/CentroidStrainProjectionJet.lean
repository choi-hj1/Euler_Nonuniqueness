import EulerNonuniqueness.Section3.CentroidStrainComplexGauge
import EulerNonuniqueness.Section3.ContourCentroidTangentQuadratic

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] complexStrainGaugeC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem centroidCenteredStrain_derivative_projection (data direction : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    fderiv ℝ centroidCenteredStrain data direction = c1Conjugate (contourCentroidGaugeProjection data direction) := by
  have conjugate : HasFDerivAt (fun current => star (contourCentroidFunctional current))
      (((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ)).comp
        (fderiv ℝ contourCentroidFunctional data)) data :=
    ((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt).comp data
      (analyticAt_contourCentroidFunctional data small).differentiableAt.hasFDerivAt
  have constant := c1ConstantCLM.hasFDerivAt.comp data conjugate
  have derivative := c1ConjugateCLM.hasFDerivAt.sub constant
  have actual : HasFDerivAt centroidCenteredStrain
      (c1ConjugateCLM - c1ConstantCLM.comp
        ((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).comp
          (fderiv ℝ contourCentroidFunctional data))) data := derivative
  rw [actual.fderiv]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change star (direction.val.1 label) - star ((fderiv ℝ contourCentroidFunctional data) direction) =
    star (direction.val.1 label - (fderiv ℝ contourCentroidFunctional data) direction)
  rw [star_sub]

theorem projected_complex_strain_derivative_projection (data direction : PeriodicC1HolderHalf)
    (coefficient : ℂ) (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    fderiv ℝ (fun current : PeriodicC1HolderHalf => contourCentroidGaugeProjection current
      (coefficient • c1Conjugate current)) data direction =
      coefficient • c1Conjugate (contourCentroidGaugeProjection data direction) := by
  rw [contourCentroidGaugeProjection_complex_strain_fderiv data coefficient small,
    ContinuousLinearMap.comp_apply, centroidCenteredStrain_derivative_projection data direction small]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

theorem projected_complex_strain_same_centroid_remainder (data direction : PeriodicC1HolderHalf)
    (coefficient : ℂ)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (nextSmall : ‖data + direction - standardCircleBanach‖ < 1 / 3)
    (centered : contourCentroidFunctional (data + direction) = contourCentroidFunctional data) :
    ‖contourCentroidGaugeProjection (data + direction) (coefficient • c1Conjugate (data + direction)) -
      contourCentroidGaugeProjection data (coefficient • c1Conjugate data) -
      fderiv ℝ (fun current : PeriodicC1HolderHalf => contourCentroidGaugeProjection current
        (coefficient • c1Conjugate current)) data direction‖ ≤
      ‖coefficient‖ * ‖contourCentroidGaugeProjection data direction - direction‖ := by
  rw [contourCentroidGaugeProjection_complex_strain _ coefficient nextSmall,
    contourCentroidGaugeProjection_complex_strain _ coefficient small,
    projected_complex_strain_derivative_projection data direction coefficient small]
  have difference : centroidCenteredStrain (data + direction) - centroidCenteredStrain data = c1Conjugate direction := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (star (data.val.1 label + direction.val.1 label) - star (contourCentroidFunctional (data + direction))) -
      (star (data.val.1 label) - star (contourCentroidFunctional data)) = star (direction.val.1 label)
    rw [centered, star_add]
    abel
  rw [← smul_sub, difference, ← smul_sub, norm_smul]
  have conjugates : c1Conjugate direction - c1Conjugate (contourCentroidGaugeProjection data direction) =
      c1Conjugate (direction - contourCentroidGaugeProjection data direction) := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    exact (star_sub _ _).symm
  rw [conjugates]
  exact mul_le_mul_of_nonneg_left ((c1Conjugate_norm_bound _).trans_eq (norm_sub_rev _ _)) (norm_nonneg coefficient)

theorem projected_complex_strain_derivative_norm_bound (data : PeriodicC1HolderHalf)
    (coefficient : ℂ) (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    ‖fderiv ℝ (fun current : PeriodicC1HolderHalf => contourCentroidGaugeProjection current
      (coefficient • c1Conjugate current)) data‖ ≤ ‖coefficient‖ * ‖contourCentroidGaugeProjection data‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  rw [projected_complex_strain_derivative_projection data direction coefficient small, norm_smul]
  exact (mul_le_mul_of_nonneg_left
    ((c1Conjugate_norm_bound _).trans ((contourCentroidGaugeProjection data).le_opNorm direction))
    (norm_nonneg coefficient)).trans_eq (by ring)

end EulerNonuniqueness.Paper
