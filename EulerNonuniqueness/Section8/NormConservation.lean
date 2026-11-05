import EulerNonuniqueness.Section8.PowerConservation

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem tendsto_integral_norm_rpow_one {source : Vorticity}
    (integrable : Integrable source) (member : MemLp source 2 volume) :
    Tendsto (fun index : ℕ => ∫ position, ‖source position‖ ^ (1 + 1 / ((index : ℝ) + 1))) atTop
      (𝓝 (∫ position, ‖source position‖)) := by
  have exponentLimit : Tendsto (fun index : ℕ => 1 + 1 / ((index : ℝ) + 1)) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
  have target : (fun position => ‖source position‖ ^ (1 : ℝ)) = (fun position => ‖source position‖) := by
    funext position
    exact Real.rpow_one _
  rw [← target]
  apply tendsto_integral_of_dominated_convergence (fun position => ‖source position‖ + ‖source position‖ ^ (2 : ℕ))
  · intro index
    exact (Real.continuous_rpow_const (by positivity : 0 ≤ 1 + 1 / ((index : ℝ) + 1))).comp_aestronglyMeasurable
      integrable.aestronglyMeasurable.norm
  · exact integrable.norm.add (member.integrable_norm_pow (by norm_num))
  · intro index
    exact Filter.Eventually.of_forall fun position => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      have lower : 1 ≤ 1 + 1 / ((index : ℝ) + 1) := le_add_of_nonneg_right (by positivity)
      have upper : 1 + 1 / ((index : ℝ) + 1) ≤ 2 := by
        have : 1 / ((index : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) index])
        linarith
      by_cases small : ‖source position‖ ≤ 1
      · have estimate := Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (source position)) small zero_le_one lower
        simp only [Real.rpow_one] at estimate
        exact estimate.trans (le_add_of_nonneg_right (sq_nonneg _))
      · have estimate := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge small) upper
        rw [Real.rpow_two] at estimate
        exact estimate.trans (le_add_of_nonneg_left (norm_nonneg _))
  · exact Filter.Eventually.of_forall fun position =>
      (Real.continuousAt_const_rpow' (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp exponentLimit

theorem TransportAnalyticHypotheses.integral_norm_eq_zero_time
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    (∫ position, ‖omega time position‖) = ∫ position, ‖omega 0 position‖ := by
  have endpointLimit := tendsto_integral_norm_rpow_one (hypotheses.integrable inside) (hypotheses.weakL2Continuous.1 time inside)
  have zeroLimit := tendsto_integral_norm_rpow_one (hypotheses.integrable ⟨le_rfl, positive.le⟩)
    (hypotheses.weakL2Continuous.1 0 ⟨le_rfl, positive.le⟩)
  apply tendsto_nhds_unique endpointLimit
  apply zeroLimit.congr
  intro index
  have strict : 1 < 1 + 1 / ((index : ℝ) + 1) := by
    have reciprocalPositive : 0 < 1 / ((index : ℝ) + 1) := by positivity
    linarith
  exact (hypotheses.integral_norm_rpow_eq_zero_time positive
    strict inside).symm

theorem TransportAnalyticHypotheses.eLpNorm_eq_initial
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon)
    {exponent : ℝ} (exponentBound : 1 ≤ exponent) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    eLpNorm (omega time) (ENNReal.ofReal exponent) volume = eLpNorm initial (ENNReal.ofReal exponent) volume := by
  have initialEquality := eLpNorm_congr_ae (p := ENNReal.ofReal exponent) (hypotheses.initial_ae_eq positive)
  apply Eq.trans ?_ initialEquality
  rcases eq_or_lt_of_le exponentBound with equality | strict
  · subst exponent
    simp only [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm]
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hypotheses.integrable inside),
      ← ofReal_integral_norm_eq_lintegral_enorm (hypotheses.integrable ⟨le_rfl, positive.le⟩),
      hypotheses.integral_norm_eq_zero_time positive inside]
  · exact hypotheses.eLpNorm_eq_zero_time_of_one_lt positive strict inside

end EulerNonuniqueness
