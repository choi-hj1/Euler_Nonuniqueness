import EulerNonuniqueness.Section3.ContourDerivativeHolomorphic

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

def contourCauchySecondVariation (data first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) : PeriodicHolderHalf :=
  deriv (fun parameter : ℂ =>
    contourCauchyDirectionalDerivative (data + parameter • second) first density) 0

theorem contourCauchySecondVariation_hasDerivAt
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    HasDerivAt (fun parameter : ℂ =>
      contourCauchyDirectionalDerivative (data + parameter • second) first density)
      (contourCauchySecondVariation data first second density) 0 :=
  (analyticAt_contourCauchyDirectionalDerivative_complex_line
    data first second density small).differentiableAt.hasDerivAt

theorem contourCauchySecondVariation_value
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    (contourCauchySecondVariation data first second density).val.1 target =
      2 * contourCauchyQuadraticIntegral data first second density target := by
  have vector := (complexHolderEvaluation target).hasFDerivAt.comp_hasDerivAt (0 : ℂ)
    (contourCauchySecondVariation_hasDerivAt data first second density small)
  exact vector.unique
    (contourCauchyDirectionalDerivative_evaluation_hasDerivAt_zero
      data first second density small target)

theorem contourCauchySecondVariation_symm
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourCauchySecondVariation data first second density =
      contourCauchySecondVariation data second first density := by
  apply PeriodicHolderHalf.ext_value
  intro target
  rw [contourCauchySecondVariation_value data first second density small,
    contourCauchySecondVariation_value data second first density small,
    contourCauchyQuadraticIntegral_symm]

theorem contourCauchySecondVariation_add_left
    (data first second third : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourCauchySecondVariation data (first + second) third density =
      contourCauchySecondVariation data first third density +
        contourCauchySecondVariation data second third density := by
  apply PeriodicHolderHalf.ext_value
  intro target
  change (contourCauchySecondVariation data (first + second) third density).val.1 target =
    (contourCauchySecondVariation data first third density).val.1 target +
      (contourCauchySecondVariation data second third density).val.1 target
  rw [contourCauchySecondVariation_value data (first + second) third density small,
    contourCauchySecondVariation_value data first third density small,
    contourCauchySecondVariation_value data second third density small,
    contourCauchyQuadraticIntegral_add_left data first second third density
      (small.trans_le (min_le_right _ _))]
  ring

theorem contourCauchySecondVariation_smul_left
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℂ) :
    contourCauchySecondVariation data (scalar • first) second density =
      scalar • contourCauchySecondVariation data first second density := by
  apply PeriodicHolderHalf.ext_value
  intro target
  change (contourCauchySecondVariation data (scalar • first) second density).val.1 target =
    scalar * (contourCauchySecondVariation data first second density).val.1 target
  rw [contourCauchySecondVariation_value data (scalar • first) second density small,
    contourCauchySecondVariation_value data first second density small,
    contourCauchyQuadraticIntegral_smul_left]
  ring

end

end EulerNonuniqueness.Paper
