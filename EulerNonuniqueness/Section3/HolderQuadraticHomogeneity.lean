import EulerNonuniqueness.Section3.HolderQuotientCubicTaylor

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem holderInverseQuadratic_real_smul (data increment : PeriodicHolderHalf) (scalar : ℝ) :
    holderInverseQuadratic data (scalar • increment) = scalar ^ 2 • holderInverseQuadratic data increment := by
  apply PeriodicHolderHalf.ext_value
  intro label
  change ((scalar : ℂ) * increment.val.1 label) *
      (((scalar : ℂ) * increment.val.1 label) * ((extendedHolderInverse data).val.1 label *
        ((extendedHolderInverse data).val.1 label * (extendedHolderInverse data).val.1 label))) =
    ((scalar ^ 2 : ℝ) : ℂ) * (increment.val.1 label *
      (increment.val.1 label * ((extendedHolderInverse data).val.1 label *
        ((extendedHolderInverse data).val.1 label * (extendedHolderInverse data).val.1 label))))
  push_cast
  ring

theorem holderQuotientQuadratic_real_smul (data increment : PeriodicHolderHalf) (scalar : ℝ) :
    holderQuotientQuadratic data (scalar • increment) = scalar ^ 2 • holderQuotientQuadratic data increment := by
  have linear_scaled : holderInverseDerivativeCLM data (scalar • increment) =
      scalar • holderInverseDerivativeCLM data increment :=
    (holderInverseDerivativeCLM data).map_smul scalar increment
  unfold holderQuotientQuadratic
  rw [holderInverseQuadratic_real_smul, linear_scaled]
  apply PeriodicHolderHalf.ext_value
  intro label
  change star (data.val.1 label) *
      (((scalar ^ 2 : ℝ) : ℂ) * (holderInverseQuadratic data increment).val.1 label) +
      star ((scalar : ℂ) * increment.val.1 label) *
        ((scalar : ℂ) * (holderInverseDerivativeCLM data increment).val.1 label) =
    ((scalar ^ 2 : ℝ) : ℂ) *
      (star (data.val.1 label) * (holderInverseQuadratic data increment).val.1 label +
        star (increment.val.1 label) * (holderInverseDerivativeCLM data increment).val.1 label)
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal]
  push_cast
  ring

end

end EulerNonuniqueness.Paper
