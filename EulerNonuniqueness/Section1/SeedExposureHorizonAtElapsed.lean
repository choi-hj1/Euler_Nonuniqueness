import EulerNonuniqueness.Section1.PolynomialSeedSmallness
import EulerNonuniqueness.Section5.Delay

noncomputable section
open Filter
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper

theorem Scales.eventually_seed_exposure_horizon_at_elapsed (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (alphaSmall : scales.alpha < 1) {sectionTime endpoint : ℝ}
    (sectionPositive : 0 < sectionTime) (endpointPositive : 0 < endpoint) (endpointOne : endpoint ≤ 1)
    (elapsedMin : ℝ) (elapsedPositive : 0 < elapsedMin) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ, 1 ≤ index →
      let changed : Scales := {scales with frequency := frequency}
      let growth := 2 * Real.sqrt 2 * changed.omega index
      let horizon := Real.log (endpoint / changed.seed index) / growth
      0 < horizon ∧ horizon < 1 / 4 ∧ elapsedMin ≤ growth * horizon ∧
        changed.seed index * Real.exp (growth * horizon) = endpoint ∧
        ∀ time : ℝ, 0 ≤ time → time ≤ horizon →
          changed.seed index * Real.exp (growth * time) ≤ endpoint := by
  have ratioOne : 1 < scales.ratio := by linarith
  filter_upwards [scales.eventually_polynomial_seed_rpow_lt ratioBound alphaPositive 0
      (by norm_num : (0 : ℝ) < 1) (mul_pos endpointPositive (Real.exp_pos (-elapsedMin))),
    scales.eventually_actual_delay_total_lt ratioOne alphaSmall sectionTime (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_gt_atTop (0 : ℝ)] with frequency tiny total frequencyPositive
  let changed : Scales := {scales with frequency := frequency}
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have seedPositive (index : ℕ) : 0 < changed.seed index := changed.seed_pos frequencyPositive ratioPositive index
  have seedTiny (index : ℕ) : changed.seed index < endpoint * Real.exp (-elapsedMin) := by
    simpa only [pow_zero, Real.rpow_one, one_mul] using tiny index
  have seedOne (index : ℕ) : changed.seed index < 1 := by
    have exponential : Real.exp (-elapsedMin : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [elapsedPositive])
    have bound : endpoint * Real.exp (-elapsedMin) ≤ endpoint := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left exponential endpointPositive.le
    exact (seedTiny index).trans_le (bound.trans endpointOne)
  intro index indexOne
  let growth := 2 * Real.sqrt 2 * changed.omega index
  let horizon := Real.log (endpoint / changed.seed index) / growth
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive index
  have growthPositive : 0 < growth := by dsimp only [growth]; positivity
  have ratioEndpoint : 0 < endpoint / changed.seed index := div_pos endpointPositive (seedPositive index)
  have logarithm : elapsedMin < Real.log (endpoint / changed.seed index) := by
    apply (Real.exp_lt_exp).mp
    rw [Real.exp_log ratioEndpoint]
    apply (lt_div_iff₀ (seedPositive index)).mpr
    have scaled := mul_lt_mul_of_pos_left (seedTiny index) (Real.exp_pos (elapsedMin : ℝ))
    have cancel : Real.exp (elapsedMin : ℝ) * (endpoint * Real.exp (-elapsedMin)) = endpoint := by
      rw [mul_left_comm, ← Real.exp_add]
      rw [add_neg_cancel, Real.exp_zero, mul_one]
    rw [cancel] at scaled
    exact scaled
  have positive : 0 < horizon := div_pos (by linarith) growthPositive
  have growthIdentity : growth * horizon = Real.log (endpoint / changed.seed index) := by
    dsimp only [horizon]
    field_simp
  have delayBound : horizon ≤ changed.delay sectionTime index := by
    have logs : Real.log (endpoint / changed.seed index) ≤ Real.log (1 / changed.seed index) :=
      Real.log_le_log ratioEndpoint (div_le_div_of_nonneg_right endpointOne (seedPositive index).le)
    have scaled := div_le_div_of_nonneg_right logs growthPositive.le
    have extra : 0 ≤ sectionTime / changed.omega index := div_nonneg sectionPositive.le omegaPositive.le
    change horizon ≤ changed.delay sectionTime index
    unfold Scales.delay
    dsimp only [horizon, growth] at scaled ⊢
    have identity : (Real.log (1 / changed.seed index) / (2 * Real.sqrt 2) + sectionTime) /
        changed.omega index = Real.log (1 / changed.seed index) / (2 * Real.sqrt 2 * changed.omega index) +
        sectionTime / changed.omega index := by ring
    rw [identity]
    linarith only [scaled, extra]
  have summable := changed.actual_delay_summable frequencyPositive ratioOne alphaSmall sectionTime
  have term := summable.le_tsum (index - 1) (fun next _ =>
    (changed.actual_delay_pos frequencyPositive ratioPositive sectionPositive (next + 1) (seedOne _)).le)
  have indexIdentity : index - 1 + 1 = index := by omega
  rw [indexIdentity] at term
  have identity : changed.seed index * Real.exp (growth * horizon) = endpoint := by
    rw [growthIdentity, Real.exp_log ratioEndpoint]
    field_simp [(seedPositive index).ne']
  refine ⟨positive, delayBound.trans_lt (term.trans_lt total), ?_, identity, ?_⟩
  · rw [growthIdentity]
    exact logarithm.le
  · intro time _ timeBound
    rw [← identity]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left timeBound growthPositive.le)) (seedPositive index).le

end EulerNonuniqueness.Paper
