import EulerNonuniqueness.Section3.ContourCauchyFrechet
import EulerNonuniqueness.Section3.C1HolderBanachAlgebra

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem banachContourVelocity_eq_cauchy (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    banachContourVelocity data target = Complex.I / 4 * data.val.1 target -
      (1 / (4 * Real.pi) : ℂ) * star
        (contourCauchyTransform data.val.1 data.val.2.val.1
          (fun source => star (data.val.1 source)) target) := by
  let density : PeriodicHolderHalf := holderConjugate (c1ValueHolder data)
  have integrable := contourCauchyDensityRemainder_intervalIntegrable data density
    (small.trans_le (min_le_right _ _)) target
  have conjugate_integral := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm integrable
  change (∫ source in (target - Real.pi)..(target + Real.pi),
    star (contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 target source)) =
    star (∫ source in (target - Real.pi)..(target + Real.pi),
      contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 target source) at conjugate_integral
  have integral_identity :
      (∫ source in (target - Real.pi)..(target + Real.pi),
        contourChordPhase data.val.1 target source * star (data.val.2.val.1 source)) =
      -star (∫ source in (target - Real.pi)..(target + Real.pi),
        contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 target source) := by
    rw [← conjugate_integral, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro source _
    change contourChordPhase data.val.1 target source * star (data.val.2.val.1 source) =
      -star ((star (data.val.1 source) - star (data.val.1 target)) * data.val.2.val.1 source /
        (data.val.1 target - data.val.1 source))
    unfold contourChordPhase
    simp only [Complex.star_def, map_div₀, map_mul, map_sub, Complex.conj_conj]
    ring
  rw [banachContourVelocity_eq_phase data small target, integral_identity]
  change (1 / (4 * Real.pi)) •
    (-star (∫ source in (target - Real.pi)..(target + Real.pi),
      contourCauchyDensityRemainder data.val.1 data.val.2.val.1
        (fun label => star (data.val.1 label)) target source)) = _
  unfold contourCauchyTransform
  rw [Complex.real_smul]
  simp only [star_sub, star_mul, star_star, Complex.star_def, map_natCast, Complex.conj_I,
    Complex.conj_ofReal]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

def holderContourVelocity (data : PeriodicC1HolderHalf) : PeriodicHolderHalf :=
  (Complex.I / 4) • c1ValueHolder data - (1 / (4 * Real.pi) : ℂ) •
    holderConjugate (extendedContourCauchy data (holderConjugate (c1ValueHolder data)))

theorem holderContourVelocity_value (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    (holderContourVelocity data).val.1 target = banachContourVelocity data target := by
  rw [banachContourVelocity_eq_cauchy data small target]
  unfold holderContourVelocity
  change Complex.I / 4 * data.val.1 target - (1 / (4 * Real.pi) : ℂ) *
    star ((extendedContourCauchy data (holderConjugate (c1ValueHolder data))).val.1 target) = _
  rw [extendedContourCauchy_eq _ _ small, contourCauchyOperator_value]
  rfl

end

end EulerNonuniqueness.Paper
