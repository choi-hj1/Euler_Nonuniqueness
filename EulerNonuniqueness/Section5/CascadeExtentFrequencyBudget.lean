import EulerNonuniqueness.Section5.CascadeExtentScalarBudget
import EulerNonuniqueness.Section5.CascadeGeometricScaleSmallness
import EulerNonuniqueness.Section1.UniformTransportScaleSmallness
import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_extent_gronwall_budget (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {factor : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      let changed : Scales := {scales with frequency := frequency}
      (4 / Real.pi) * (24 / factor) ^ 2 * changed.strain ≤ Real.log (4 / 3) ∧
      10 * changed.omega index * changed.length index / factor +
        (512 / Real.pi) * (24 / factor) ^ 3 * changed.radius index ^ 2 * changed.hessian ≤
          changed.location index / 1000 := by
  let first : ℝ := 10 / factor
  let second : ℝ := (512 / Real.pi) * (24 / factor) ^ 3
  let rate : ℝ := (4 / Real.pi) * (24 / factor) ^ 2
  let tolerance : ℝ := 1 / (1000 * (first + second))
  have firstPositive : 0 < first := by dsimp [first]; positivity
  have secondPositive : 0 < second := by dsimp [second]; positivity
  have ratePositive : 0 < rate := by dsimp [rate]; positivity
  have tolerancePositive : 0 < tolerance := by dsimp [tolerance]; positivity
  have logPositive : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have rateTolerancePositive : 0 < Real.log (4 / 3) / rate := div_pos logPositive ratePositive
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_omega_length_lt_location ratioBound alphaPositive tolerancePositive,
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds tolerancePositive),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds rateTolerancePositive),
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      factorPositive factorSmall (by norm_num : (3 : ℝ) ≤ 3)]
    with frequency frequencyBound transport hessianSmall strainSmall geometry index
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (changed.location_pos _).le _)
  have radiusNonnegative : 0 ≤ changed.radius index := Real.sqrt_nonneg _
  have locationPositive := changed.location_pos index
  have radiusSmall : changed.radius index ≤ changed.location index := by
    have estimate := (geometry index).2.2.2
    change changed.radius index ≤ changed.location index / 1000 at estimate
    linarith
  have squareBound : changed.radius index ^ 2 ≤ changed.location index := by
    have firstBound := pow_le_pow_left₀ radiusNonnegative radiusSmall 2
    have lastBound := mul_le_mul_of_nonneg_left (changed.location_le_one index) locationPositive.le
    nlinarith
  have transportBound : first * (changed.omega index * changed.length index) ≤
      first * (tolerance * changed.location index) :=
    mul_le_mul_of_nonneg_left (transport index).le firstPositive.le
  have hessianBound : second * changed.radius index ^ 2 * changed.hessian ≤
      second * changed.location index * tolerance := by
    calc
      _ ≤ second * changed.location index * changed.hessian :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left squareBound secondPositive.le) hessianNonnegative
      _ ≤ _ := mul_le_mul_of_nonneg_left hessianSmall.le (mul_nonneg secondPositive.le locationPositive.le)
  have totalIdentity : first * (tolerance * changed.location index) +
      second * changed.location index * tolerance = changed.location index / 1000 := by
    dsimp only [tolerance]
    field_simp [(add_pos firstPositive secondPositive).ne']
    <;> ring
  refine ⟨?_, ?_⟩
  · have estimate := (lt_div_iff₀ ratePositive).mp strainSmall
    change rate * changed.strain ≤ _
    linarith
  · have actual := add_le_add transportBound hessianBound
    rw [totalIdentity] at actual
    simpa only [first, second, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using actual

end EulerNonuniqueness.Paper
