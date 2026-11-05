import EulerNonuniqueness.Section3.ContourScalarGreen

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem integral_nearCircleInterior_wirtingerBar
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (function : ℂ → ℂ) (derivative : ℂ → ℂ →L[ℝ] ℂ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ position, HasFDerivAt function (derivative position) position) :
    (∫ position in nearCircleInterior data small,
      (derivative position 1 + Complex.I * derivative position Complex.I) / 2) =
      (-Complex.I / 2) * ∫ label in (-Real.pi)..Real.pi,
        function (data.val.1 label) * data.val.2.val.1 label := by
  let conjugation : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ
  let firstDerivative := fun position => conjugation.comp (derivative position)
  let secondDerivative := fun position => Complex.I • firstDerivative position
  have firstGreen := integral_nearCircleInterior_divergence data small
    (fun position => star (function position)) firstDerivative
    functionContinuous.star (continuous_const.clm_comp derivativeContinuous)
    (fun position => conjugation.hasFDerivAt.comp position (functionDerivative position))
  have secondGreen := integral_nearCircleInterior_divergence data small
    (fun position => Complex.I * star (function position)) secondDerivative
    (continuous_const.mul functionContinuous.star)
    (continuous_const.smul (continuous_const.clm_comp derivativeContinuous))
    (fun position => (conjugation.hasFDerivAt.comp position
      (functionDerivative position)).const_smul Complex.I)
  have interiorIntegrable := nearCircleInterior_integrable_of_continuous data small
    (fun position => (derivative position 1 + Complex.I * derivative position Complex.I) / 2)
    (by fun_prop)
  have boundaryIntegrable : IntervalIntegrable
      (fun label => function (data.val.1 label) * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi :=
    ((functionContinuous.comp data.val.1.continuous).mul data.val.2.val.1.continuous).intervalIntegrable _ _
  have firstTrace (position : ℂ) : contourPlaneTrace (firstDerivative position) =
      (derivative position 1).re - (derivative position Complex.I).im := by
    simp [firstDerivative, conjugation, contourPlaneTrace, sub_eq_add_neg]
  have secondTrace (position : ℂ) : contourPlaneTrace (secondDerivative position) =
      (derivative position 1).im + (derivative position Complex.I).re := by
    simp [secondDerivative, firstDerivative, conjugation, contourPlaneTrace,
      Complex.mul_re, Complex.mul_im]
  simp_rw [firstTrace] at firstGreen
  simp_rw [secondTrace] at secondGreen
  have realBoundary (value : ℂ) : ((-Complex.I / 2) * value).re = value.im / 2 := by
    simp [Complex.mul_re]
    <;> ring
  have imaginaryBoundary (value : ℂ) : ((-Complex.I / 2) * value).im = -value.re / 2 := by
    simp [Complex.mul_im]
    <;> ring
  apply Complex.ext
  · change Complex.reCLM _ = _
    rw [← Complex.reCLM.integral_comp_comm interiorIntegrable]
    rw [realBoundary]
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.I_mul_re, Complex.reCLM_apply,
      ← sub_eq_add_neg]
    rw [integral_div, firstGreen]
    have boundaryReal := Complex.imCLM.intervalIntegral_comp_comm boundaryIntegrable
    change (∫ label in (-Real.pi)..Real.pi,
      (function (data.val.1 label) * data.val.2.val.1 label).im) =
        (∫ label in (-Real.pi)..Real.pi,
          function (data.val.1 label) * data.val.2.val.1 label).im at boundaryReal
    change (∫ label in (-Real.pi)..Real.pi,
      contourAreaPair (star (function (data.val.1 label))) (data.val.2.val.1 label)) / 2 = _
    rw [← boundaryReal]
    congr 1
    apply intervalIntegral.integral_congr
    intro label _
    simp [contourAreaPair, Complex.imCLM_apply]
    <;> ring
  · change Complex.imCLM _ = _
    rw [← Complex.imCLM.integral_comp_comm interiorIntegrable]
    rw [imaginaryBoundary]
    simp only [Complex.div_ofNat_im, Complex.add_im, Complex.I_mul_im, Complex.imCLM_apply]
    rw [integral_div, secondGreen]
    have boundaryReal := Complex.reCLM.intervalIntegral_comp_comm boundaryIntegrable
    change (∫ label in (-Real.pi)..Real.pi,
      (function (data.val.1 label) * data.val.2.val.1 label).re) =
        (∫ label in (-Real.pi)..Real.pi,
          function (data.val.1 label) * data.val.2.val.1 label).re at boundaryReal
    rw [← boundaryReal]
    rw [← intervalIntegral.integral_neg]
    congr 1
    apply intervalIntegral.integral_congr
    intro label _
    simp [contourAreaPair, Complex.mul_re, Complex.mul_im, Complex.reCLM_apply]
    <;> ring

end EulerNonuniqueness.Paper
