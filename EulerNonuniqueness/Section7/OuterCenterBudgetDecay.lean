import EulerNonuniqueness.Section4.OuterDisplacementDecay

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.outer_center_budget_tendsto_zero (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (constant : ℝ) :
    Tendsto (fun frequency : ℝ =>
      let changed := {scales with frequency := frequency}
      constant * (Real.exp (constant * changed.strain) *
          (changed.hessian * changed.omega 1 ^ 2 * changed.length 1 +
            changed.hessian * changed.length 1 / changed.omega 1 ^ 4) +
        changed.hessian * changed.omega 1 ^ 2 * changed.length 1 +
        (changed.omega 1)⁻¹ ^ 4 +
        (∑' source : ℕ, changed.circulation (source + 2)) / changed.length 1)) atTop (𝓝 0) := by
  have ratioPositive : 0 < scales.ratio := by linarith
  have quadratic := scales.weighted_exponential_point_tendsto_zero ratioPositive alphaPositive 1 2
    (coefficient := 1) zero_lt_one
  simp only [Real.rpow_two, one_mul, neg_mul] at quadratic
  change Tendsto (fun frequency : ℝ => ({scales with frequency := frequency}).omega 1 ^ 2 *
    ({scales with frequency := frequency}).length 1) atTop (𝓝 0) at quadratic
  have hessian := scales.hessian_tendsto_zero ratioBound alphaPositive
  have length := scales.length_frequency_tendsto_zero ratioPositive alphaPositive 1
  have inverseFourth := (tendsto_inv_atTop_zero.comp (scales.omega_frequency_tendsto_atTop ratioPositive 1)).pow 4
  have strainExp : Tendsto (fun frequency : ℝ => Real.exp
      (constant * ({scales with frequency := frequency}).strain)) atTop (𝓝 (Real.exp (constant * 0))) :=
    Real.continuous_exp.continuousAt.tendsto.comp
      ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul constant)
  have primary := hessian.mul quadratic
  have remainder := (hessian.mul length).mul inverseFourth
  have tail := scales.tail_circulation_div_length_one_tendsto_zero (by linarith) alphaPositive
  have combined := ((((strainExp.mul (primary.add remainder)).add primary).add inverseFourth).add tail).const_mul constant
  simpa only [zero_mul, mul_zero, zero_add, add_zero, zero_pow (by norm_num : 4 ≠ 0), Real.exp_zero, one_mul, Function.comp_apply,
    div_eq_mul_inv, inv_pow, mul_assoc] using combined

theorem Scales.eventually_outer_center_budget_lt (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (constant : ℝ)
    {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop,
      let changed := {scales with frequency := frequency}
      constant * (Real.exp (constant * changed.strain) *
          (changed.hessian * changed.omega 1 ^ 2 * changed.length 1 +
            changed.hessian * changed.length 1 / changed.omega 1 ^ 4) +
        changed.hessian * changed.omega 1 ^ 2 * changed.length 1 +
        (changed.omega 1)⁻¹ ^ 4 +
        (∑' source : ℕ, changed.circulation (source + 2)) / changed.length 1) < tolerance :=
  (scales.outer_center_budget_tendsto_zero ratioBound alphaPositive constant).eventually
    (eventually_lt_nhds tolerancePositive)

end EulerNonuniqueness.Paper
