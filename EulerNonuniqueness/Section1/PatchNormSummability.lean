import EulerNonuniqueness.Section1.ScaleLpSummability

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.patch_Lp_envelope_le (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) {exponent : ℝ} (exponentPositive : 0 < exponent)
    (index : ℕ) (omegaLarge : 1 ≤ scales.omega index) :
    scales.amplitude * scales.omega index ^ 4 * (Real.pi * scales.radius index ^ 2) ^ (1 / exponent) ≤
      (scales.amplitude * (2 * Real.pi / scales.amplitude) ^ (1 / exponent)) *
        (scales.omega index ^ (4 : ℝ) * Real.exp (-(2 / exponent) * scales.omega index ^ scales.alpha)) := by
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  have cubeLarge : 1 ≤ scales.omega index ^ 3 := one_le_pow₀ omegaLarge
  have areaEquality : Real.pi * scales.radius index ^ 2 =
      ((2 * Real.pi / scales.amplitude) * Real.exp (-2 * scales.omega index ^ scales.alpha)) /
        scales.omega index ^ 3 := by
    rw [scales.radius_sq amplitudePositive frequencyPositive ratioPositive, scales.length_sq]
    field_simp
    ring
  have areaBound : Real.pi * scales.radius index ^ 2 ≤
      (2 * Real.pi / scales.amplitude) * Real.exp (-2 * scales.omega index ^ scales.alpha) := by
    rw [areaEquality]
    exact div_le_self (by positivity) cubeLarge
  have powerBound := Real.rpow_le_rpow (show 0 ≤ Real.pi * scales.radius index ^ 2 by positivity)
    areaBound (show 0 ≤ 1 / exponent by positivity)
  have estimate := mul_le_mul_of_nonneg_left powerBound
    (show 0 ≤ scales.amplitude * scales.omega index ^ 4 by positivity)
  rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul] at estimate
  have exponentEquality : -(2 / exponent) * scales.omega index ^ scales.alpha =
      -2 * scales.omega index ^ scales.alpha * (1 / exponent) := by ring
  have quarticPower : scales.omega index ^ (4 : ℝ) = scales.omega index ^ (4 : ℕ) :=
    Real.rpow_natCast _ _
  simpa only [quarticPower, exponentEquality, mul_assoc, mul_left_comm, mul_comm] using estimate

theorem Scales.patch_Lp_envelope_summable (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioGreaterOne : 1 < scales.ratio) (alphaPositive : 0 < scales.alpha)
    {exponent : ℝ} (exponentPositive : 0 < exponent) :
    Summable (fun index : ℕ => scales.amplitude * scales.omega index ^ 4 *
      (Real.pi * scales.radius index ^ 2) ^ (1 / exponent)) := by
  have envelope := (scales.weighted_exponential_summable frequencyPositive ratioGreaterOne
    alphaPositive 4 (show 0 < 2 / exponent by positivity)).mul_left
      (scales.amplitude * (2 * Real.pi / scales.amplitude) ^ (1 / exponent))
  apply Summable.of_norm_bounded_eventually_nat _ envelope
  filter_upwards [(scales.omega_tendsto frequencyPositive ratioGreaterOne).eventually (eventually_ge_atTop 1)]
    with index omegaLarge
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact scales.patch_Lp_envelope_le amplitudePositive frequencyPositive
    (zero_lt_one.trans ratioGreaterOne) exponentPositive index omegaLarge

end EulerNonuniqueness.Paper
