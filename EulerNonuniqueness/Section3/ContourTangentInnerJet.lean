import EulerNonuniqueness.Section3.ContourCauchyDensityJet
import EulerNonuniqueness.Section3.ContourQuotientCubicTaylor

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def contourTangentInner (data : PeriodicC1HolderHalf) : PeriodicHolderHalf :=
  extendedContourCauchy data (extendedContourTangentQuotient data) +
    ((Real.pi : ℂ) * Complex.I) • extendedContourTangentQuotient data

def contourTangentInnerLinear (data increment : PeriodicC1HolderHalf) : PeriodicHolderHalf :=
  contourCauchyDirectionalDerivative data increment (extendedContourTangentQuotient data) +
    extendedContourCauchy data (contourQuotientDerivativeCLM data increment) +
    ((Real.pi : ℂ) * Complex.I) • (contourQuotientDerivativeCLM data increment)

def contourTangentInnerQuadratic (data increment : PeriodicC1HolderHalf) : PeriodicHolderHalf :=
  (1 / 2 : ℂ) • contourCauchySecondVariation data increment increment
      (extendedContourTangentQuotient data) +
    contourCauchyDirectionalDerivative data increment (contourQuotientDerivativeCLM data increment) +
    extendedContourCauchy data (contourQuotientQuadratic data increment) +
    ((Real.pi : ℂ) * Complex.I) • contourQuotientQuadratic data increment

theorem contourTangentInner_remainder_identity (data increment : PeriodicC1HolderHalf) :
    contourTangentInner (data + increment) - contourTangentInner data -
        contourTangentInnerLinear data increment - contourTangentInnerQuadratic data increment =
      (extendedContourCauchy (data + increment) (extendedContourTangentQuotient (data + increment)) -
        extendedContourCauchy data (extendedContourTangentQuotient data) -
        (contourCauchyDirectionalDerivative data increment (extendedContourTangentQuotient data) +
          extendedContourCauchy data (contourQuotientDerivativeCLM data increment)) -
        ((1 / 2 : ℂ) • contourCauchySecondVariation data increment increment
            (extendedContourTangentQuotient data) +
          contourCauchyDirectionalDerivative data increment (contourQuotientDerivativeCLM data increment) +
          extendedContourCauchy data (contourQuotientQuadratic data increment))) +
      ((Real.pi : ℂ) * Complex.I) •
        (extendedContourTangentQuotient (data + increment) - extendedContourTangentQuotient data -
          contourQuotientDerivativeCLM data increment - contourQuotientQuadratic data increment) := by
  unfold contourTangentInner contourTangentInnerLinear contourTangentInnerQuadratic
  simp only [smul_sub]
  abel

theorem contourTangentInner_remainder_bound (data increment : PeriodicC1HolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi)))
    (increment_small : ‖increment‖ ≤ (radius - ‖data - standardCircleBanach‖) / 4) :
    ‖contourTangentInner (data + increment) - contourTangentInner data -
      contourTangentInnerLinear data increment - contourTangentInnerQuadratic data increment‖ ≤
      (16 * (contourCauchyUniformOperatorConstant radius * ‖extendedContourTangentQuotient data‖) /
        (radius - ‖data - standardCircleBanach‖) ^ 3) * ‖increment‖ ^ 3 +
      (8 * (contourCauchyUniformOperatorConstant radius * ‖contourQuotientDerivativeCLM data increment‖) /
        (radius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 2 +
      contourCauchyParameterOperatorConstant radius * ‖increment‖ * ‖contourQuotientQuadratic data increment‖ +
      (contourCauchyUniformOperatorConstant radius + Real.pi) *
        ‖extendedContourTangentQuotient (data + increment) - extendedContourTangentQuotient data -
          contourQuotientDerivativeCLM data increment - contourQuotientQuadratic data increment‖ := by
  rw [contourTangentInner_remainder_identity]
  apply (norm_add_le _ _).trans
  have bound := contourCauchy_density_jet_remainder_bound data increment
    (extendedContourTangentQuotient data) (contourQuotientDerivativeCLM data increment)
    (contourQuotientQuadratic data increment) (extendedContourTangentQuotient (data + increment))
    near small increment_small
  have scalar_norm : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
  rw [norm_smul ((Real.pi : ℂ) * Complex.I)
    (extendedContourTangentQuotient (data + increment) - extendedContourTangentQuotient data -
      contourQuotientDerivativeCLM data increment - contourQuotientQuadratic data increment), scalar_norm]
  exact (add_le_add_right bound _).trans_eq (by ring)

end

end EulerNonuniqueness.Paper
