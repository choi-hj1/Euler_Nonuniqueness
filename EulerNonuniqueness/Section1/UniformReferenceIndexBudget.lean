import EulerNonuniqueness.Section1.ExternalFieldScaleBounds
import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_uniform_reference_index_budget_small (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {constant tolerance : ℝ} (constantNonnegative : 0 ≤ constant) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      let changed : Scales := {scales with frequency := frequency}
      0 ≤ constant * ((changed.strain + changed.strain ^ 2) / changed.omega index + (changed.omega index)⁻¹ ^ 5) ∧
      constant * ((changed.strain + changed.strain ^ 2) / changed.omega index + (changed.omega index)⁻¹ ^ 5) < tolerance := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 + 3 * constant / tolerance),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyOne frequencyLarge strainSmall
  intro index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega index
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have omegaFrequency : frequency ≤ omega := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) index
  have omegaOne : 1 ≤ omega := frequencyOne.trans omegaFrequency
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have strainBudget : changed.strain + changed.strain ^ 2 ≤ 2 := by nlinarith [strainSmall.le]
  have inverseBound : omega⁻¹ ^ 5 ≤ omega⁻¹ := by
    have inverseNonnegative : 0 ≤ omega⁻¹ := inv_nonneg.mpr omegaPositive.le
    have inverseOne : omega⁻¹ ≤ 1 := inv_le_one_of_one_le₀ omegaOne
    have power : omega⁻¹ ^ 4 ≤ 1 := pow_le_one₀ inverseNonnegative inverseOne
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right power inverseNonnegative).trans_eq (by ring)
  have envelope : (changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5 ≤ 3 / omega := by
    have actual := add_le_add (div_le_div_of_nonneg_right strainBudget omegaPositive.le) inverseBound
    exact actual.trans_eq (by rw [← one_div]; ring)
  have positiveSlack : 3 * constant < tolerance * omega := by
    have actual := mul_le_mul_of_nonneg_left (frequencyLarge.trans omegaFrequency) tolerancePositive.le
    have identity : tolerance * (1 + 3 * constant / tolerance) = tolerance + 3 * constant := by field_simp
    rw [identity] at actual
    linarith
  have final : constant * (3 / omega) < tolerance := by
    have actual := (div_lt_iff₀ omegaPositive).mpr positiveSlack
    exact (show constant * (3 / omega) = 3 * constant / omega by ring).trans_lt actual
  refine ⟨?_, ?_⟩
  · exact mul_nonneg constantNonnegative (add_nonneg
      (div_nonneg (add_nonneg strainNonnegative (sq_nonneg _)) omegaPositive.le)
      (pow_nonneg (inv_nonneg.mpr omegaPositive.le) _))
  · exact (mul_le_mul_of_nonneg_left envelope constantNonnegative).trans_lt final

end EulerNonuniqueness.Paper
