import EulerNonuniqueness.Section3.ContourComplexGreen

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem integral_nearCircleInterior_wirtinger
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (function : ℂ → ℂ) (derivative : ℂ → ℂ →L[ℝ] ℂ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ position, HasFDerivAt function (derivative position) position) :
    (∫ position in nearCircleInterior data small,
      (derivative position 1 - Complex.I * derivative position Complex.I) / 2) =
      (Complex.I / 2) * ∫ label in (-Real.pi)..Real.pi,
        function (data.val.1 label) * star (data.val.2.val.1 label) := by
  let conjugation : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ
  let conjugateDerivative := fun position => conjugation.comp (derivative position)
  have green := integral_nearCircleInterior_wirtingerBar data small
    (fun position => star (function position)) conjugateDerivative functionContinuous.star
    (continuous_const.clm_comp derivativeContinuous)
    (fun position => conjugation.hasFDerivAt.comp position (functionDerivative position))
  have interiorIdentity (position : ℂ) :
      (conjugateDerivative position 1 + Complex.I * conjugateDerivative position Complex.I) / 2 =
        star ((derivative position 1 - Complex.I * derivative position Complex.I) / 2) := by
    simp [conjugateDerivative, conjugation, map_div₀, map_sub, Complex.star_def, Complex.conj_I]
    <;> ring
  simp_rw [interiorIdentity] at green
  have interiorIntegrable := nearCircleInterior_integrable_of_continuous data small
    (fun position => (derivative position 1 - Complex.I * derivative position Complex.I) / 2)
    (by fun_prop)
  have interiorConjugate := conjugation.integral_comp_comm interiorIntegrable
  change (∫ position in nearCircleInterior data small,
    star ((derivative position 1 - Complex.I * derivative position Complex.I) / 2)) =
      star (∫ position in nearCircleInterior data small,
        (derivative position 1 - Complex.I * derivative position Complex.I) / 2) at interiorConjugate
  rw [interiorConjugate] at green
  have boundaryIntegrable : IntervalIntegrable
      (fun label => function (data.val.1 label) * star (data.val.2.val.1 label))
      volume (-Real.pi) Real.pi :=
    ((functionContinuous.comp data.val.1.continuous).mul
      data.val.2.val.1.continuous.star).intervalIntegrable _ _
  have boundaryIdentity :
      (∫ label in (-Real.pi)..Real.pi,
        star (function (data.val.1 label)) * data.val.2.val.1 label) =
      star (∫ label in (-Real.pi)..Real.pi,
        function (data.val.1 label) * star (data.val.2.val.1 label)) := by
    have commutation := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm boundaryIntegrable
    change (∫ label in (-Real.pi)..Real.pi,
      star (function (data.val.1 label) * star (data.val.2.val.1 label))) =
        star (∫ label in (-Real.pi)..Real.pi,
          function (data.val.1 label) * star (data.val.2.val.1 label)) at commutation
    simpa only [star_mul, star_star, mul_comm] using commutation
  rw [boundaryIdentity] at green
  have actual := congrArg (fun value : ℂ => star value) green
  simpa only [Complex.star_def, Complex.conj_conj, map_mul, map_div₀, map_neg,
    Complex.conj_I, map_ofNat, neg_neg] using actual

end EulerNonuniqueness.Paper
