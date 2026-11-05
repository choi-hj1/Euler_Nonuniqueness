import EulerNonuniqueness.Section5.CascadeExtentFrequencyBudget

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_anchor_speed_budget (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {factor : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      let changed : Scales := {scales with frequency := frequency}
      5 * changed.omega index * changed.length index / factor +
        (256 / Real.pi) * (24 / factor) ^ 3 * changed.radius index ^ 2 * changed.hessian +
        (2 / Real.pi) * (24 / factor) *
          (∑' source : ℕ, changed.circulation (source + 1) / changed.location (source + 1)) ≤ 1 / 4 := by
  let first : ℝ := 5 / factor
  let second : ℝ := (256 / Real.pi) * (24 / factor) ^ 3
  let third : ℝ := (2 / Real.pi) * (24 / factor)
  let tolerance : ℝ := 1 / (4 * (first + second + third))
  have firstPositive : 0 < first := by dsimp [first]; positivity
  have secondPositive : 0 < second := by dsimp [second]; positivity
  have thirdPositive : 0 < third := by dsimp [third]; positivity
  have totalPositive : 0 < first + second + third := by positivity
  have tolerancePositive : 0 < tolerance := by dsimp [tolerance]; positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_omega_length_lt_location ratioBound alphaPositive tolerancePositive,
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds tolerancePositive),
    (scales.circulation_location_total_tendsto_zero ratioBound alphaPositive 1).eventually
      (eventually_lt_nhds tolerancePositive),
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      factorPositive factorSmall (by norm_num : (3 : ℝ) ≤ 3)]
    with frequency frequencyBound transport hessianSmall totalSmall geometry index
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (changed.location_pos _).le _)
  have radiusNonnegative : 0 ≤ changed.radius index := Real.sqrt_nonneg _
  have radiusOne : changed.radius index ≤ 1 := by
    have estimate := (geometry index).2.2.2
    change changed.radius index ≤ changed.location index / 1000 at estimate
    linarith [changed.location_le_one index]
  have squareOne : changed.radius index ^ 2 ≤ 1 := by nlinarith
  have transportOne : changed.omega index * changed.length index ≤ tolerance :=
    (transport index).le.trans (mul_le_of_le_one_right tolerancePositive.le (changed.location_le_one index))
  have firstBound := mul_le_mul_of_nonneg_left transportOne firstPositive.le
  have secondBound : second * changed.radius index ^ 2 * changed.hessian ≤ second * tolerance := by
    have bounded := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left squareOne secondPositive.le) hessianNonnegative
    exact bounded.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hessianSmall.le secondPositive.le)
  have thirdBound := mul_le_mul_of_nonneg_left totalSmall.le thirdPositive.le
  have identity : first * tolerance + second * tolerance + third * tolerance = (1 / 4 : ℝ) := by
    dsimp only [tolerance]
    field_simp [totalPositive.ne']
    <;> ring
  have actual := add_le_add (add_le_add firstBound secondBound) thirdBound
  rw [identity] at actual
  simpa only [first, second, third, pow_one, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using actual

end EulerNonuniqueness.Paper
