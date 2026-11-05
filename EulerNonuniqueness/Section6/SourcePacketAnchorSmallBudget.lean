import EulerNonuniqueness.Section5.CascadeExtentFrequencyBudget

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_source_packet_anchor_small_budget (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {factor tolerance : ℝ} (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop,
    let changed := {scales with frequency := frequency}
    (∀ index : ℕ, 10 * changed.omega index * changed.length index / factor +
      (512 / Real.pi) * (24 / factor) ^ 3 * changed.radius index ^ 2 * changed.hessian ≤
        tolerance * changed.location index / 1000) ∧
    (2 / Real.pi) * (24 / factor) ^ 2 * changed.strain ≤ tolerance / 64 ∧
    (144 / (Real.pi * factor)) * changed.strain ≤ tolerance / 32 := by
  let first : ℝ := 10 / factor
  let second : ℝ := (512 / Real.pi) * (24 / factor) ^ 3
  let budget : ℝ := tolerance / (1000 * (first + second))
  have firstPositive : 0 < first := by dsimp only [first]; positivity
  have secondPositive : 0 < second := by dsimp only [second]; positivity
  have sumPositive : 0 < first + second := by positivity
  have budgetPositive : 0 < budget := by dsimp only [budget]; positivity
  have firstStrain := (scales.strain_tendsto_zero ratioBound alphaPositive).const_mul ((2 / Real.pi) * (24 / factor) ^ 2)
  have secondStrain := (scales.strain_tendsto_zero ratioBound alphaPositive).const_mul (144 / (Real.pi * factor))
  simp only [mul_zero] at firstStrain secondStrain
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_omega_length_lt_location ratioBound alphaPositive budgetPositive,
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds budgetPositive),
    firstStrain.eventually (eventually_lt_nhds (show (0 : ℝ) < tolerance / 64 by positivity)),
    secondStrain.eventually (eventually_lt_nhds (show (0 : ℝ) < tolerance / 32 by positivity)),
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      factorPositive factorSmall (by norm_num : (3 : ℝ) ≤ 3)]
    with frequency frequencyOne transport hessianSmall firstSmall secondSmall geometry
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
  refine ⟨?_, firstSmall.le, secondSmall.le⟩
  intro index
  have radiusNonnegative : 0 ≤ changed.radius index := Real.sqrt_nonneg _
  have radiusLocation : changed.radius index ≤ changed.location index := by
    have actual := (geometry index).2.2.2
    linarith [changed.location_pos index]
  have radiusOne : changed.radius index ≤ 1 := radiusLocation.trans (changed.location_le_one index)
  have radiusSquare : changed.radius index ^ 2 ≤ changed.location index := by nlinarith
  have transportBound := mul_le_mul_of_nonneg_left (transport index).le firstPositive.le
  have hessianBound := mul_le_mul radiusSquare hessianSmall.le hessianNonnegative (changed.location_pos index).le
  have secondBound := mul_le_mul_of_nonneg_left hessianBound secondPositive.le
  have identity : first * (budget * changed.location index) + second * (changed.location index * budget) =
      tolerance * changed.location index / 1000 := by
    dsimp only [budget]
    field_simp [sumPositive.ne']
    <;> ring
  have combined := add_le_add transportBound secondBound
  have completed := combined.trans_eq identity
  simpa only [first, second, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using completed

end EulerNonuniqueness.Paper
