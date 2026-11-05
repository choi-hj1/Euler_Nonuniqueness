import EulerNonuniqueness.Section1.AdjacentReturnFrequencyGain
import EulerNonuniqueness.Section5.UniformSeedSmallness

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.adjacent_returned_incoming_seed_budget_le (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    {coefficient rho : ℝ} (coefficientPositive : 0 < coefficient) (rhoNonnegative : 0 ≤ rho) (index : ℕ) :
    rho / (scales.omega index * scales.location index ^ 4) *
        (scales.circulation (index + 1) * scales.length (index + 1) ^ 2 *
          (1 + (scales.location (index + 1))⁻¹) / (coefficient * scales.omega (index + 1))) ≤
      (3 / coefficient) * (rho / scales.frequency) * (scales.seed index / scales.ratio ^ 2) := by
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  have locationPositive := scales.location_pos (index + 1)
  have omegaNext : scales.omega (index + 1) = scales.omega index * scales.ratio := by
    simp only [Scales.omega, pow_succ]
    ring
  have locationPrevious : scales.location index = 2 * scales.location (index + 1) := by
    rw [scales.location_eq_inv_pow, scales.location_eq_inv_pow, pow_succ]
    field_simp
  have normalization :
      scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
          (scales.omega (index + 1) * scales.location index ^ 4) =
        (Real.pi * Real.sqrt 2 / (16 * Real.sqrt 3)) * (scales.seed index / scales.ratio ^ 2) := by
    simp only [Scales.seed, scales.adjacent_location_distance, Scales.circulation, omegaNext]
    rw [locationPrevious]
    field_simp [ratioPositive.ne', omegaPositive.ne', locationPositive.ne', Real.pi_ne_zero,
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne',
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']
    ring
  have sqrtTwo : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have sqrtThree : (1 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have numeric : Real.pi * Real.sqrt 2 / (16 * Real.sqrt 3) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16) (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)))).mpr
    have product := mul_le_mul Real.pi_lt_four.le sqrtTwo (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith only [product, sqrtThree]
  have seedNonnegative : 0 ≤ scales.seed index / scales.ratio ^ 2 := by
    exact div_nonneg (scales.seed_pos frequencyPositive ratioPositive index).le (sq_nonneg _)
  have sourceBound : scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
      (scales.omega (index + 1) * scales.location index ^ 4) ≤ scales.seed index / scales.ratio ^ 2 := by
    rw [normalization]
    exact mul_le_of_le_one_left seedNonnegative numeric
  have frequencyBound : scales.frequency ≤ scales.omega index := by
    change scales.frequency ≤ scales.frequency * scales.ratio ^ index
    exact le_mul_of_one_le_right frequencyPositive.le (one_le_pow₀ (by linarith only [ratioBound]))
  have inverseBound : 1 / scales.omega index ≤ 1 / scales.frequency :=
    one_div_le_one_div_of_le frequencyPositive frequencyBound
  have gainBound : 1 / scales.omega index + 1 / (scales.omega index * scales.location (index + 1)) ≤
      3 / scales.frequency := by
    have adjacent := scales.adjacent_return_frequency_gain_le frequencyPositive ratioBound index
    calc
      _ ≤ 1 / scales.frequency + 2 / scales.frequency := add_le_add inverseBound adjacent
      _ = _ := by ring
  have gainNonnegative : 0 ≤ 1 / scales.omega index + 1 / (scales.omega index * scales.location (index + 1)) := by positivity
  have comparison := mul_le_mul sourceBound gainBound gainNonnegative seedNonnegative
  have scaled := mul_le_mul_of_nonneg_left comparison (div_nonneg rhoNonnegative coefficientPositive.le)
  convert scaled using 1 <;> field_simp [coefficientPositive.ne', omegaPositive.ne', locationPositive.ne',
    ratioPositive.ne', frequencyPositive.ne', (scales.location_pos index).ne'] <;> ring

theorem Scales.eventually_adjacent_returned_incoming_seed_budget_small (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {coefficient tolerance : ℝ} (coefficientPositive : 0 < coefficient) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      let changed : Scales := {scales with frequency := frequency}
      let rho := 216360000 * changed.hessian + 576 * changed.strain
      rho / (changed.omega index * changed.location index ^ 4) *
          (changed.circulation (index + 1) * changed.length (index + 1) ^ 2 *
            (1 + (changed.location (index + 1))⁻¹) / (coefficient * changed.omega (index + 1))) <
        tolerance * (changed.seed index / changed.ratio ^ 2) := by
  have rhoDecay := ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
    ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576)
  simp only [mul_zero, zero_add] at rhoDecay
  have decay := (tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).const_mul (3 / coefficient)
  simp only [mul_zero] at decay
  filter_upwards [eventually_gt_atTop (0 : ℝ), rhoDecay.eventually (eventually_lt_nhds zero_lt_one),
    decay.eventually (eventually_lt_nhds tolerancePositive)] with frequency frequencyPositive rhoSmall small index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
    dsimp only [rho]
    positivity
  have estimate := changed.adjacent_returned_incoming_seed_budget_le frequencyPositive ratioBound coefficientPositive rhoNonnegative index
  have scalar : (3 / coefficient) * (rho / frequency) < tolerance := by
    have upper := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right rhoSmall.le frequencyPositive.le) (by positivity : (0 : ℝ) ≤ 3 / coefficient)
    exact upper.trans_lt (by simpa only [one_div] using small)
  exact estimate.trans_lt (mul_lt_mul_of_pos_right scalar
    (div_pos (changed.seed_pos frequencyPositive ratioPositive index) (sq_pos_of_pos ratioPositive)))

end EulerNonuniqueness.Paper
