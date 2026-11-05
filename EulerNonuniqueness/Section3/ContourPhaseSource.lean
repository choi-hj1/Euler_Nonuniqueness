import EulerNonuniqueness.Section3.ContourTangentQuotient

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem banachContourPhaseSource_measurable (data : PeriodicC1HolderHalf) (target : ℝ) :
    Measurable (fun source => contourChordPhaseDerivative data.val.1 data.val.2.val.1 source target) := by
  have difference : Measurable (fun source => data.val.1 source - data.val.1 target) :=
    data.val.1.continuous.measurable.sub measurable_const
  have tangent : Measurable (fun source => data.val.2.val.1 source) := data.val.2.val.1.continuous.measurable
  have star_difference := continuous_star.measurable.comp difference
  exact ((tangent.mul star_difference).sub (difference.mul (continuous_star.measurable.comp tangent))).div
    (star_difference.pow_const 2)

theorem banachContourPhaseSource_integrable (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    IntervalIntegrable (fun source => contourChordPhaseDerivative data.val.1 data.val.2.val.1 source target)
      volume (target - Real.pi) (target + Real.pi) := by
  have chord_pos := sub_pos.mpr (small.trans_le (min_le_right _ _))
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by linarith [Real.pi_pos] : target - Real.pi ≤ target + Real.pi)).mpr
  apply weakSingular_integrable (banachContourPhaseSource_measurable data target).aestronglyMeasurable
    (center := target)
    (bound := 2 * ‖data‖ ^ 2 / (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖) ^ 2)
  intro source membership
  by_cases equal : source = target
  · subst source
    simp [contourChordPhaseDerivative, inverseSqrtDistance]
  have nearby : |source - target| ≤ 3 * Real.pi / 2 := by
    rw [abs_le]
    constructor <;> linarith [membership.1, membership.2, Real.pi_pos]
  have chord := PeriodicC1HolderHalf.chord_bound_extended data nearby
  rw [norm_sub_rev (data.val.1 target) (data.val.1 source)] at chord
  have actual := contourChordPhaseDerivative_bound equal (norm_nonneg data) (norm_nonneg data) chord_pos
    (fun current _ => PeriodicC1HolderHalf.hasDerivAt data current)
    (fun current _ => PeriodicC1HolderHalf.derivative_holder_bound data current source)
    (PeriodicC1HolderHalf.speed_bound data source) chord
  convert actual using 1 <;> simp only [inverseSqrtDistance] <;> ring

set_option maxHeartbeats 1000000 in
theorem banachContourPhaseSource_integral_zero (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    (∫ source in (target - Real.pi)..(target + Real.pi),
      contourChordPhaseDerivative data.val.1 data.val.2.val.1 source target) = 0 := by
  have chord_pos := sub_pos.mpr (small.trans_le (min_le_right _ _))
  have separated : ∀ source ∈ Icc (target - Real.pi) (target + Real.pi), source ≠ target →
      data.val.1 source - data.val.1 target ≠ 0 := by
    intro source membership distinct
    have nearby : |source - target| ≤ 3 * Real.pi / 2 := by
      rw [abs_le]
      constructor <;> linarith [membership.1, membership.2, Real.pi_pos]
    have chord := PeriodicC1HolderHalf.chord_bound_extended data nearby
    rw [norm_sub_rev (data.val.1 target) (data.val.1 source)] at chord
    exact norm_ne_zero_iff.mp (ne_of_gt ((mul_pos chord_pos (abs_pos.mpr (sub_ne_zero.mpr distinct))).trans_le chord))
  have continuous : ContinuousOn (fun source => contourChordPhaseExtension data.val.1 source target)
      (Icc (target - Real.pi) (target + Real.pi)) := by
    intro source membership
    apply ContinuousAt.continuousWithinAt
    by_cases equal : source = target
    · subst source
      exact contourChordPhaseExtension_continuousAt_diagonal (PeriodicC1HolderHalf.hasDerivAt data target)
        (PeriodicC1HolderHalf.tangent_ne_zero data small target)
    · exact (contourChordPhaseExtension_derivative equal (PeriodicC1HolderHalf.hasDerivAt data source)
        (separated source membership equal)).continuousAt
  have actual := integral_eq_sub_of_hasDerivAt_except_point
    (singular := target) (by linarith [Real.pi_pos] : target - Real.pi ≤ target + Real.pi) continuous
    (fun source membership distinct => contourChordPhaseExtension_derivative distinct
      (PeriodicC1HolderHalf.hasDerivAt data source)
      (separated source ⟨membership.1.le, membership.2.le⟩ distinct))
    (banachContourPhaseSource_integrable data small target)
  have endpoints : contourChordPhaseExtension data.val.1 (target + Real.pi) target =
      contourChordPhaseExtension data.val.1 (target - Real.pi) target := by
    rw [contourChordPhaseExtension_of_ne data.val.1 (by linarith [Real.pi_pos] : target + Real.pi ≠ target),
      contourChordPhaseExtension_of_ne data.val.1 (by linarith [Real.pi_pos] : target - Real.pi ≠ target)]
    have closed : data.val.1 (target + Real.pi) = data.val.1 (target - Real.pi) := by
      have periodic := PeriodicC1HolderHalf.periodic data (target - Real.pi)
      convert periodic using 1 <;> congr 1 <;> ring
    unfold contourChordPhase
    rw [closed]
  rw [endpoints, sub_self] at actual
  exact actual

theorem complex_phase_source_cancellation {difference first second : ℂ}
    (first_ne : first ≠ 0) (second_ne : second ≠ 0) :
    ((first * star difference - difference * star first) / (star difference ^ 2)) * star second +
      star first * ((second * star (-difference) - (-difference) * star second) / (star (-difference) ^ 2)) =
      -star first * star (((star second / second) - (star first / first)) * second / difference) := by
  by_cases difference_ne : difference = 0
  · simp [difference_ne]
  simp only [star_div, star_mul, star_sub, star_star, star_neg]
  field_simp [Complex.star_def, first_ne, second_ne, difference_ne]
  ring

theorem banachContourPhaseSource_cancellation (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target source : ℝ) :
    contourChordPhaseDerivative data.val.1 data.val.2.val.1 target source * star (data.val.2.val.1 source) +
      star (data.val.2.val.1 target) * contourChordPhaseDerivative data.val.1 data.val.2.val.1 source target =
      -star (data.val.2.val.1 target) * star (contourCauchyDensityRemainder data.val.1 data.val.2.val.1
        (contourTangentQuotient data small).val.1 target source) := by
  unfold contourCauchyDensityRemainder contourChordPhaseDerivative
  rw [contourTangentQuotient_value, contourTangentQuotient_value]
  have difference : data.val.1 source - data.val.1 target = -(data.val.1 target - data.val.1 source) := by abel
  rw [difference]
  exact complex_phase_source_cancellation (PeriodicC1HolderHalf.tangent_ne_zero data small target)
    (PeriodicC1HolderHalf.tangent_ne_zero data small source)

theorem banachContourPhaseDerivative_integral_cauchy (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    (∫ source in (target - Real.pi)..(target + Real.pi),
      contourChordPhaseDerivative data.val.1 data.val.2.val.1 target source * star (data.val.2.val.1 source)) =
      -star (data.val.2.val.1 target) * star (∫ source in (target - Real.pi)..(target + Real.pi),
        contourCauchyDensityRemainder data.val.1 data.val.2.val.1
          (contourTangentQuotient data small).val.1 target source) := by
  let remainder := contourCauchyDensityRemainder data.val.1 data.val.2.val.1
    (contourTangentQuotient data small).val.1 target
  have remainder_integrable := banachContourCauchy_density_integrable_centered data
    (contourTangentQuotient data small) small target
  have star_integrable : IntervalIntegrable (fun source => star (remainder source)) volume
      (target - Real.pi) (target + Real.pi) :=
    ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp remainder_integrable.1,
      Complex.conjCLE.toContinuousLinearMap.integrable_comp remainder_integrable.2⟩
  have star_integral : (∫ source in (target - Real.pi)..(target + Real.pi), star (remainder source)) =
      star (∫ source in (target - Real.pi)..(target + Real.pi), remainder source) :=
    Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm remainder_integrable
  have source_integrable := banachContourPhaseSource_integrable data small target
  have identity : (fun source => contourChordPhaseDerivative data.val.1 data.val.2.val.1 target source *
      star (data.val.2.val.1 source)) =
      (fun source => -star (data.val.2.val.1 target) * star (remainder source) -
        star (data.val.2.val.1 target) * contourChordPhaseDerivative data.val.1 data.val.2.val.1 source target) := by
    funext source
    have cancellation := banachContourPhaseSource_cancellation data small target source
    change _ + _ = -star (data.val.2.val.1 target) * star (remainder source) at cancellation
    linear_combination cancellation
  rw [identity, intervalIntegral.integral_sub (star_integrable.const_mul _) (source_integrable.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, star_integral,
    banachContourPhaseSource_integral_zero data small target, mul_zero, sub_zero]

end EulerNonuniqueness.Paper
