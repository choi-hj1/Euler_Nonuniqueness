import EulerNonuniqueness.Section1.UniformReferenceIndexBudget
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_uniform_reference_index_rate_small (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {constant tolerance : ℝ} (constantNonnegative : 0 ≤ constant) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      let changed : Scales := {scales with frequency := frequency}
      0 ≤ changed.omega index * (constant *
        ((changed.strain + changed.strain ^ 2) / changed.omega index + (changed.omega index)⁻¹ ^ 5)) ∧
      changed.omega index * (constant *
        ((changed.strain + changed.strain ^ 2) / changed.omega index + (changed.omega index)⁻¹ ^ 5)) < tolerance := by
  have strainDecay := scales.strain_tendsto_zero ratioBound alphaPositive
  have inverseDecay : Tendsto (fun frequency : ℝ => frequency⁻¹ ^ 4) atTop (𝓝 0) := by
    simpa only [show (0 : ℝ) ^ 4 = 0 by norm_num] using
      (tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 4
  have envelopeDecay : Tendsto (fun frequency : ℝ => constant *
      ((({scales with frequency := frequency} : Scales).strain +
        ({scales with frequency := frequency} : Scales).strain ^ 2) + frequency⁻¹ ^ 4)) atTop (𝓝 0) := by
    simpa only [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_add, mul_zero] using
      ((strainDecay.add (strainDecay.pow 2)).add inverseDecay).const_mul constant
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    envelopeDecay.eventually (eventually_lt_nhds tolerancePositive)] with frequency frequencyOne envelopeSmall
  intro index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive index
  have omegaFrequency : frequency ≤ changed.omega index :=
    changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) index
  have inverseBound : (changed.omega index)⁻¹ ≤ frequency⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le frequencyPositive omegaFrequency
  have powerBound := pow_le_pow_left₀ (inv_nonneg.mpr omegaPositive.le) inverseBound 4
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have identity : changed.omega index * (constant *
      ((changed.strain + changed.strain ^ 2) / changed.omega index + (changed.omega index)⁻¹ ^ 5)) =
      constant * (changed.strain + changed.strain ^ 2 + (changed.omega index)⁻¹ ^ 4) := by
    field_simp [omegaPositive.ne']
    ring
  rw [identity]
  refine ⟨mul_nonneg constantNonnegative (add_nonneg
    (add_nonneg strainNonnegative (sq_nonneg _)) (pow_nonneg (inv_nonneg.mpr omegaPositive.le) _)), ?_⟩
  exact (mul_le_mul_of_nonneg_left (add_le_add_left powerBound _) constantNonnegative).trans_lt envelopeSmall

theorem Scales.eventually_uniform_integrated_reference_index_budget_small (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {constant tolerance : ℝ} (constantNonnegative : 0 ≤ constant) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ, ∀ finish ∈ Icc (0 : ℝ) 1,
      let changed : Scales := {scales with frequency := frequency}
      0 ≤ (∫ _ in (0 : ℝ)..finish, changed.omega index * (constant *
        ((changed.strain + changed.strain ^ 2) / changed.omega index + (changed.omega index)⁻¹ ^ 5))) ∧
      (∫ _ in (0 : ℝ)..finish, changed.omega index * (constant *
        ((changed.strain + changed.strain ^ 2) / changed.omega index + (changed.omega index)⁻¹ ^ 5))) < tolerance := by
  filter_upwards [scales.eventually_uniform_reference_index_rate_small ratioBound alphaPositive
    constantNonnegative tolerancePositive] with frequency bounds
  intro index finish inside
  dsimp only
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  refine ⟨mul_nonneg inside.1 (bounds index).1, ?_⟩
  exact (mul_le_of_le_one_left (bounds index).1 inside.2).trans_lt (bounds index).2

end EulerNonuniqueness.Paper
