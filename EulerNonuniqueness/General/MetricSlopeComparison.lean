import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem norm_slope_le_of_split_increment
    (curve main : ℝ → Space) {base later rate : ℝ} (after : base < later)
    (increment : ‖curve later - curve base - (main later - main base)‖ ≤ rate * (later - base)) :
    slope (fun time => ‖curve time‖) base later ≤ ‖slope main base later‖ + rate := by
  have differencePositive : 0 < later - base := sub_pos.mpr after
  have splitBound : ‖curve later - curve base‖ ≤ ‖main later - main base‖ + rate * (later - base) := by
    have identity : curve later - curve base =
        (main later - main base) + (curve later - curve base - (main later - main base)) := by abel
    calc
      _ = ‖(main later - main base) + (curve later - curve base - (main later - main base))‖ := congrArg norm identity
      _ ≤ ‖main later - main base‖ + ‖curve later - curve base - (main later - main base)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_left increment _
  have normBound := (norm_sub_norm_le (curve later) (curve base)).trans splitBound
  have mainSlope : ‖slope main base later‖ = ‖main later - main base‖ / (later - base) := by
    rw [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos differencePositive]
    ring
  rw [mainSlope, slope_def_field]
  apply (div_le_iff₀ differencePositive).mpr
  have cancellation : (‖main later - main base‖ / (later - base) + rate) * (later - base) =
      ‖main later - main base‖ + rate * (later - base) := by field_simp
  rw [cancellation]
  exact normBound

theorem eventually_norm_slope_lt_of_split_increment
    {curve main : ℝ → Space} {base rate : ℝ} {velocity : Space}
    (derivative : HasDerivAt main velocity base)
    (increment : ∀ᶠ later in 𝓝[>] base,
      ‖curve later - curve base - (main later - main base)‖ ≤ rate * (later - base))
    {threshold : ℝ} (strict : ‖velocity‖ + rate < threshold) :
    ∀ᶠ later in 𝓝[>] base, slope (fun time => ‖curve time‖) base later < threshold := by
  have slopes : Tendsto (slope main base) (𝓝[>] base) (𝓝 velocity) := by
    have actual := hasDerivWithinAt_iff_tendsto_slope.mp (derivative.hasDerivWithinAt (s := Ici base))
    rwa [Ici_diff_left] at actual
  have smallSlope : ∀ᶠ later in 𝓝[>] base, ‖slope main base later‖ < threshold - rate :=
    slopes.norm.eventually (eventually_lt_nhds (by linarith : ‖velocity‖ < threshold - rate))
  filter_upwards [increment, smallSlope, eventually_mem_nhdsWithin] with later errorBound slopeBound after
  exact (norm_slope_le_of_split_increment curve main after errorBound).trans_lt (by linarith)

theorem norm_le_linear_bound_of_split_increments
    {curve : ℝ → Space} {initial terminal bound : ℝ}
    (continuous : ContinuousOn curve (Icc initial terminal))
    (increments : ∀ base ∈ Ico initial terminal,
      ∃ main : ℝ → Space, ∃ velocity : Space, ∃ rate : ℝ,
        HasDerivAt main velocity base ∧ ‖velocity‖ + rate ≤ bound ∧
        ∀ᶠ later in 𝓝[>] base,
          ‖curve later - curve base - (main later - main base)‖ ≤ rate * (later - base)) :
    ∀ time ∈ Icc initial terminal, ‖curve time‖ ≤ ‖curve initial‖ + bound * (time - initial) := by
  apply image_le_of_liminf_slope_right_le_deriv_boundary continuous.norm
    (show ‖curve initial‖ ≤ ‖curve initial‖ + bound * (initial - initial) by simp)
    (continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
    (fun base _inside => ((hasDerivAt_id base).sub_const initial).const_mul bound |>.const_add ‖curve initial‖ |>.hasDerivWithinAt)
  intro base inside threshold strict
  simp only [mul_one] at strict
  obtain ⟨main, velocity, rate, derivative, boundRate, increment⟩ := increments base inside
  exact (eventually_norm_slope_lt_of_split_increment derivative increment (boundRate.trans_lt strict)).frequently

end EulerNonuniqueness.General
