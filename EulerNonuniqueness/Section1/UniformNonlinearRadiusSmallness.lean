import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.omega_mul_relative_patch_area (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : ℕ) :
    scales.omega index * (scales.radius index ^ 2 / scales.length index ^ 2) =
      2 / (scales.amplitude * scales.omega index ^ 2) := by
  rw [scales.radius_sq amplitudePositive frequencyPositive ratioPositive]
  field_simp [amplitudePositive.ne', (scales.length_pos index).ne',
    (scales.omega_pos frequencyPositive ratioPositive index).ne']
  ring

theorem Scales.eventually_uniform_omega_relative_patch_area_small (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 1 ≤ scales.ratio)
    {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      let changed : Scales := {scales with frequency := frequency}
      0 ≤ changed.omega index * (changed.radius index ^ 2 / changed.length index ^ 2) ∧
      changed.omega index * (changed.radius index ^ 2 / changed.length index ^ 2) < tolerance := by
  have envelopeLimit : Tendsto (fun frequency : ℝ => 2 / (scales.amplitude * frequency ^ 2)) atTop (𝓝 0) := by
    have inverseLimit := ((tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 2).const_mul
      (2 / scales.amplitude)
    convert inverseLimit using 1
    · ext frequency
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    · norm_num
  filter_upwards [eventually_ge_atTop (1 : ℝ), envelopeLimit.eventually (eventually_lt_nhds tolerancePositive)]
    with frequency frequencyOne envelopeSmall index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := zero_lt_one.trans_le ratioBound
  rw [changed.omega_mul_relative_patch_area amplitudePositive frequencyPositive ratioPositive]
  have omegaFrequency := changed.omega_ge_frequency frequencyPositive ratioBound index
  have denominatorPositive : 0 < scales.amplitude * frequency ^ 2 := by positivity
  have denominatorBound : scales.amplitude * frequency ^ 2 ≤ scales.amplitude * changed.omega index ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ frequencyPositive.le omegaFrequency 2) amplitudePositive.le
  refine ⟨by positivity, ?_⟩
  exact (div_le_div_of_nonneg_left (by norm_num) denominatorPositive denominatorBound).trans_lt envelopeSmall

end EulerNonuniqueness.Paper
