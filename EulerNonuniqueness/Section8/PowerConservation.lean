import EulerNonuniqueness.Section8.PowerRenormalization

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem tendsto_integral_powerRenormalization {source : Vorticity} {exponent : ℝ}
    (exponentBound : 1 < exponent) (membership : MemLp source (ENNReal.ofReal exponent) volume) :
    Tendsto (fun index => ∫ position, powerRenormalization exponent index (source position)) atTop
      (𝓝 (∫ position, ‖source position‖ ^ exponent)) := by
  apply tendsto_integral_of_dominated_convergence (fun position => ‖source position‖ ^ exponent)
  · intro index
    exact (powerRenormalization_admissible exponentBound index).1.continuous.comp_aestronglyMeasurable
      membership.aestronglyMeasurable
  · simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ exponent)] using
      membership.integrable_norm_rpow (by positivity : ENNReal.ofReal exponent ≠ 0) (by simp)
  · intro index
    exact Filter.Eventually.of_forall fun position => powerRenormalization_norm_le exponent index (source position)
  · exact Filter.Eventually.of_forall fun position => tendsto_powerRenormalization exponent (source position)

theorem TransportAnalyticHypotheses.integral_norm_rpow_eq_zero_time
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon)
    {exponent : ℝ} (exponentBound : 1 < exponent) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    (∫ position, ‖omega time position‖ ^ exponent) = ∫ position, ‖omega 0 position‖ ^ exponent := by
  have zeroInside : (0 : ℝ) ∈ Icc 0 horizon := ⟨le_rfl, positive.le⟩
  have endpointLimit := tendsto_integral_powerRenormalization exponentBound
    (hypotheses.membership exponent exponentBound.le time inside)
  have zeroLimit := tendsto_integral_powerRenormalization exponentBound
    (hypotheses.membership exponent exponentBound.le 0 zeroInside)
  have equality (index : ℕ) : (∫ position, powerRenormalization exponent index (omega time position)) =
      ∫ position, powerRenormalization exponent index (omega 0 position) :=
    (hypotheses.integral_renormalization_eq_initial positive (powerRenormalization_admissible exponentBound index)
      (powerRenormalization_zero (by linarith) index) inside).trans
        (hypotheses.integral_renormalization_eq_initial positive (powerRenormalization_admissible exponentBound index)
          (powerRenormalization_zero (by linarith) index) zeroInside).symm
  exact tendsto_nhds_unique endpointLimit (zeroLimit.congr fun index => (equality index).symm)

theorem TransportAnalyticHypotheses.eLpNorm_eq_zero_time_of_one_lt
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon)
    {exponent : ℝ} (exponentBound : 1 < exponent) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    eLpNorm (omega time) (ENNReal.ofReal exponent) volume = eLpNorm (omega 0) (ENNReal.ofReal exponent) volume := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by positivity : ENNReal.ofReal exponent ≠ 0) (by simp)
      (hypotheses.membership exponent exponentBound.le time inside),
    MemLp.eLpNorm_eq_integral_rpow_norm (by positivity : ENNReal.ofReal exponent ≠ 0) (by simp)
      (hypotheses.membership exponent exponentBound.le 0 ⟨le_rfl, positive.le⟩)]
  simp only [ENNReal.toReal_ofReal (by linarith : 0 ≤ exponent)]
  rw [hypotheses.integral_norm_rpow_eq_zero_time positive exponentBound inside]

end EulerNonuniqueness
