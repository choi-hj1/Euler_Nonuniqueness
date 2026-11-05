import EulerNonuniqueness.Section1.UniformInitialScaleSmallness
import EulerNonuniqueness.Section1.ExternalFieldScaleBounds

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_reference_source_packet_budgets (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {constant separationFactor : ℝ}
    (constantNonnegative : 0 ≤ constant) (factorPositive : 0 < separationFactor) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ, ∀ distance : ℝ,
      separationFactor * scales.location (index + 1) ≤ distance → distance ≤ 1 →
      let changed : Scales := {scales with frequency := frequency}
      0 < changed.frequency ∧ 0 < distance ∧
      changed.length (index + 1) / distance ≤ 1 / 1048576 ∧
      1 ≤ changed.omega (index + 1) ∧
      constant * changed.strain ≤ changed.omega index ∧
      (constant * changed.hessian) * distance ≤ 1 / 16384 ∧
      constant * changed.hessian * changed.length (index + 1) ^ 2 * 2 *
        Real.exp (2 * (constant * changed.strain)) ≤ changed.length (index + 1) ∧
      changed.radius (index + 1) ≤ changed.length (index + 1) ∧
      changed.radius (index + 1) * (1 + constant * (changed.omega (index + 1))⁻¹ ^ 2) ≤
        changed.length (index + 1) ∧
      constant * (changed.omega (index + 1))⁻¹ ^ 2 ≤ 1 / 16 := by
  have strainLimit : Tendsto (fun frequency : ℝ => constant * ({scales with frequency := frequency}).strain) atTop (𝓝 0) := by
    simpa only [mul_zero] using (scales.strain_tendsto_zero ratioBound alphaPositive).const_mul constant
  have hessianLimit : Tendsto (fun frequency : ℝ => constant * ({scales with frequency := frequency}).hessian) atTop (𝓝 0) := by
    simpa only [mul_zero] using (scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul constant
  have inverseLimit : Tendsto (fun frequency : ℝ => constant * frequency⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      ((tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 2).const_mul constant
  have hessianTolerance : 0 < min (1 / 16384 : ℝ) (1 / (2 * Real.exp 2)) := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    strainLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hessianLimit.eventually (eventually_lt_nhds hessianTolerance),
    inverseLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    scales.eventually_length_lt_location ratioBound alphaPositive (show 0 < separationFactor / 1048576 by positivity),
    scales.eventually_radius_lt_length amplitudePositive (show 1 ≤ scales.ratio by linarith)
      (by norm_num : (0 : ℝ) < 1 / 2)]
    with frequency frequencyLarge strainSmall hessianSmall inverseSmall lengths radii index distance separated distanceSmall
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyLarge
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have omegaBound (order : ℕ) : frequency ≤ changed.omega order :=
    changed.omega_ge_frequency frequencyPositive (by dsimp only [changed]; linarith) order
  have omegaPositive (order : ℕ) : 0 < changed.omega order :=
    changed.omega_pos frequencyPositive ratioPositive order
  have lengthPositive := changed.length_pos (index + 1)
  have lengthOne := changed.length_le_one frequencyPositive ratioPositive (index + 1)
  have distancePositive : 0 < distance := (mul_pos factorPositive (scales.location_pos _)).trans_le separated
  have sourceSmall : changed.length (index + 1) / distance ≤ 1 / 1048576 := by
    apply (div_le_iff₀ distancePositive).mpr
    have actual := (lengths (index + 1)).le
    change changed.length (index + 1) ≤ separationFactor / 1048576 * scales.location (index + 1) at actual
    calc
      _ ≤ separationFactor / 1048576 * scales.location (index + 1) := actual
      _ = (separationFactor * scales.location (index + 1)) / 1048576 := by ring
      _ ≤ distance / 1048576 := div_le_div_of_nonneg_right separated (by norm_num)
      _ = _ := by ring
  have strainBound : constant * changed.strain ≤ 1 := strainSmall.le
  have hessianBound : constant * changed.hessian ≤ min (1 / 16384 : ℝ) (1 / (2 * Real.exp 2)) := hessianSmall.le
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun order =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (changed.location_pos _).le _)
  have deformationBound : constant * (changed.omega (index + 1))⁻¹ ^ 2 ≤ 1 / 16 := by
    apply le_trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr (omegaPositive _).le)
        (inv_anti₀ frequencyPositive (omegaBound (index + 1))) 2) constantNonnegative)
    exact inverseSmall.le
  have exponentialBound : Real.exp (2 * (constant * changed.strain)) ≤ Real.exp 2 :=
    Real.exp_le_exp.mpr (by linarith)
  have neutralBound : constant * changed.hessian * changed.length (index + 1) ^ 2 * 2 *
      Real.exp (2 * (constant * changed.strain)) ≤ changed.length (index + 1) := by
    have lengthSquare : changed.length (index + 1) ^ 2 ≤ changed.length (index + 1) := by nlinarith
    have coefficient : constant * changed.hessian * (2 * Real.exp 2) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 2 * Real.exp 2)).mp (hessianBound.trans (min_le_right _ _))
    calc
      _ ≤ constant * changed.hessian * changed.length (index + 1) * 2 * Real.exp 2 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left lengthSquare (mul_nonneg constantNonnegative hessianNonnegative)) (by norm_num))
          exponentialBound (Real.exp_pos _).le (by positivity)
      _ = (constant * changed.hessian * (2 * Real.exp 2)) * changed.length (index + 1) := by ring
      _ ≤ 1 * changed.length (index + 1) := mul_le_mul_of_nonneg_right coefficient lengthPositive.le
      _ = _ := one_mul _
  have radiusHalf : changed.radius (index + 1) ≤ changed.length (index + 1) / 2 := by
    simpa only [one_div, inv_mul_eq_div] using (radii (index + 1)).le
  have materialRadius : changed.radius (index + 1) *
      (1 + constant * (changed.omega (index + 1))⁻¹ ^ 2) ≤ changed.length (index + 1) := by
    have radiusNonnegative := (changed.radius_pos amplitudePositive frequencyPositive ratioPositive (index + 1)).le
    calc
      _ ≤ changed.radius (index + 1) * 2 := mul_le_mul_of_nonneg_left (by linarith) radiusNonnegative
      _ ≤ _ := by linarith
  refine ⟨frequencyPositive, distancePositive, sourceSmall, frequencyLarge.trans (omegaBound _),
    strainBound.trans (frequencyLarge.trans (omegaBound _)), ?_, neutralBound, by linarith, materialRadius, deformationBound⟩
  exact (mul_le_mul_of_nonneg_left distanceSmall (mul_nonneg constantNonnegative hessianNonnegative)).trans
    (by simpa only [mul_one] using hessianBound.trans (min_le_left _ _))

end EulerNonuniqueness.Paper
