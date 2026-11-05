import EulerNonuniqueness.Section3.ContourCauchyJointCubicTaylor
import EulerNonuniqueness.Section3.ContourVelocityDerivativeValue

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def contourVelocityHolderQuadratic (data increment : PeriodicC1HolderHalf) : PeriodicHolderHalf :=
  -(1 / (4 * Real.pi) : ℂ) • holderConjugate
    ((1 / 2 : ℂ) • contourCauchySecondVariation data increment increment
        (holderConjugate (c1ValueHolder data)) +
      contourCauchyDirectionalDerivative data increment (holderConjugate (c1ValueHolder increment)))

theorem contourVelocityHolder_quadratic_remainder_identity
    (data increment : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    holderContourVelocity (data + increment) - holderContourVelocity data -
        contourVelocityHolderDerivativeCLM data near small increment -
        contourVelocityHolderQuadratic data increment =
      -(1 / (4 * Real.pi) : ℂ) • holderConjugate
        (extendedContourCauchy (data + increment)
            (holderConjugate (c1ValueHolder data) + holderConjugate (c1ValueHolder increment)) -
          extendedContourCauchy data (holderConjugate (c1ValueHolder data)) -
          (contourCauchyDirectionalDerivative data increment (holderConjugate (c1ValueHolder data)) +
            extendedContourCauchy data (holderConjugate (c1ValueHolder increment))) -
          ((1 / 2 : ℂ) • contourCauchySecondVariation data increment increment
              (holderConjugate (c1ValueHolder data)) +
            contourCauchyDirectionalDerivative data increment (holderConjugate (c1ValueHolder increment)))) := by
  have density_add : holderConjugate (c1ValueHolder (data + increment)) =
      holderConjugate (c1ValueHolder data) + holderConjugate (c1ValueHolder increment) := by
    apply PeriodicHolderHalf.ext_value
    intro target
    exact star_add (data.val.1 target) (increment.val.1 target)
  apply PeriodicHolderHalf.ext_value
  intro target
  have derivative_value := contourVelocityHolderDerivativeCLM_value data increment near small target
  change (holderContourVelocity (data + increment)).val.1 target -
      (holderContourVelocity data).val.1 target -
      (contourVelocityHolderDerivativeCLM data near small increment).val.1 target -
      (contourVelocityHolderQuadratic data increment).val.1 target = _
  rw [derivative_value]
  unfold holderContourVelocity contourVelocityHolderQuadratic
  rw [density_add, extendedContourCauchy_eq data (holderConjugate (c1ValueHolder increment))
    (near.trans small)]
  change Complex.I / 4 * (data.val.1 target + increment.val.1 target) -
      (1 / (4 * Real.pi) : ℂ) * star _ -
      (Complex.I / 4 * data.val.1 target - (1 / (4 * Real.pi) : ℂ) * star _) -
      (Complex.I / 4 * increment.val.1 target - (1 / (4 * Real.pi) : ℂ) * star _) -
      (-(1 / (4 * Real.pi) : ℂ) * star _) =
    -(1 / (4 * Real.pi) : ℂ) * star _
  change _ = -(1 / (4 * Real.pi) : ℂ) * star
    ((extendedContourCauchy (data + increment)
        (holderConjugate (c1ValueHolder data) + holderConjugate (c1ValueHolder increment))).val.1 target -
      (extendedContourCauchy data (holderConjugate (c1ValueHolder data))).val.1 target -
      ((contourCauchyDirectionalDerivative data increment (holderConjugate (c1ValueHolder data))).val.1 target +
        (contourCauchyOperatorCLM data (near.trans small)
          (holderConjugate (c1ValueHolder increment))).val.1 target) -
      ((1 / 2 : ℂ) • contourCauchySecondVariation data increment increment
          (holderConjugate (c1ValueHolder data)) +
        contourCauchyDirectionalDerivative data increment
          (holderConjugate (c1ValueHolder increment))).val.1 target)
  simp only [Complex.star_def, map_sub, map_add]
  ring

end

end EulerNonuniqueness.Paper
