import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_source_packet_fine_deformation_budget (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    {scaleRoot boundaryConstant tolerance : ℝ} (rootPositive : 0 < scaleRoot)
    (boundaryNonnegative : 0 ≤ boundaryConstant) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
    let changed := {scales with frequency := frequency}
    changed.radius index ^ 2 * (boundaryConstant / (scaleRoot ^ 2 * changed.omega index ^ 2)) ≤
      tolerance * changed.length index ^ 2 := by
  have fifthLimit : Tendsto (fun frequency : ℝ => (2 * boundaryConstant / (scales.amplitude * scaleRoot ^ 2)) * frequency⁻¹ ^ 5)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (5 : ℕ) ≠ 0), mul_zero] using
      ((tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 5).const_mul
        (2 * boundaryConstant / (scales.amplitude * scaleRoot ^ 2))
  filter_upwards [eventually_ge_atTop (1 : ℝ), fifthLimit.eventually (eventually_lt_nhds tolerancePositive)]
    with frequency frequencyOne fifthSmall index
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive index
  have omegaBound := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) index
  have inversePower := pow_le_pow_left₀ (inv_nonneg.mpr omegaPositive.le)
    (inv_anti₀ frequencyPositive omegaBound) 5
  have actual := (mul_le_mul_of_nonneg_left inversePower
    (show 0 ≤ 2 * boundaryConstant / (changed.amplitude * scaleRoot ^ 2) by positivity)).trans fifthSmall.le
  have identity : changed.radius index ^ 2 * (boundaryConstant / (scaleRoot ^ 2 * changed.omega index ^ 2)) =
      changed.length index ^ 2 * ((2 * boundaryConstant / (changed.amplitude * scaleRoot ^ 2)) * (changed.omega index)⁻¹ ^ 5) := by
    rw [changed.radius_sq amplitudePositive frequencyPositive ratioPositive]
    field_simp [amplitudePositive.ne', rootPositive.ne', omegaPositive.ne']
    <;> ring
  dsimp only
  rw [identity]
  convert mul_le_mul_of_nonneg_left actual (sq_nonneg (changed.length index)) using 1 <;> ring

end EulerNonuniqueness.Paper
