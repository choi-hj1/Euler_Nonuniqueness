import EulerNonuniqueness.General.LocalMovingNormSlope

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Parameter Space : Type*}
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem eventually_right_parameter_variation_le
    {coordinate : Parameter → ℝ → Space} {admissible : Set Parameter} {constant : ℝ}
    {parameter : ℝ → Parameter} {base rate : ℝ} {velocity : Parameter}
    (variation : ∀ᶠ later in 𝓝[>] base, ∀ first ∈ admissible, ∀ second ∈ admissible,
      ‖coordinate first later - coordinate second later‖ ≤ constant * ‖first - second‖)
    (derivative : HasDerivAt parameter velocity base)
    (initialInside : parameter base ∈ admissible)
    (nearbyInside : ∀ᶠ later in 𝓝[>] base, parameter later ∈ admissible)
    (strict : constant * ‖velocity‖ < rate) :
    ∀ᶠ later in 𝓝[>] base,
      ‖coordinate (parameter later) later - coordinate (parameter base) later‖ ≤ rate * (later - base) := by
  have slopes : Tendsto (slope parameter base) (𝓝[>] base) (𝓝 velocity) := by
    have actual := hasDerivWithinAt_iff_tendsto_slope.mp (derivative.hasDerivWithinAt (s := Ici base))
    rwa [Ici_diff_left] at actual
  have scalarLimit : Tendsto (fun later => constant * ‖slope parameter base later‖)
      (𝓝[>] base) (𝓝 (constant * ‖velocity‖)) := tendsto_const_nhds.mul slopes.norm
  filter_upwards [scalarLimit.eventually (eventually_lt_nhds strict), variation,
    nearbyInside, eventually_mem_nhdsWithin] with later small variationActual finalInside after
  have positive : 0 < later - base := sub_pos.mpr after
  have normalization : constant * ‖parameter later - parameter base‖ =
      (constant * ‖slope parameter base later‖) * (later - base) := by
    rw [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos positive]
    field_simp
  exact (variationActual _ finalInside _ initialInside).trans
    (normalization ▸ mul_le_mul_of_nonneg_right small.le positive.le)

theorem eventually_right_moving_norm_slope_lt
    {coordinate : Parameter → ℝ → Space} {admissible : Set Parameter} {constant : ℝ}
    {parameter : ℝ → Parameter} {base frozenRate threshold : ℝ} {velocity : Parameter}
    (variation : ∀ᶠ later in 𝓝[>] base, ∀ first ∈ admissible, ∀ second ∈ admissible,
      ‖coordinate first later - coordinate second later‖ ≤ constant * ‖first - second‖)
    (derivative : HasDerivAt parameter velocity base)
    (initialInside : parameter base ∈ admissible)
    (nearbyInside : ∀ᶠ later in 𝓝[>] base, parameter later ∈ admissible)
    (frozenBound : ∀ bound : ℝ, frozenRate < bound → ∀ᶠ later in 𝓝[>] base,
      slope (fun current => ‖coordinate (parameter base) current‖) base later < bound)
    (strict : frozenRate + constant * ‖velocity‖ < threshold) :
    ∀ᶠ later in 𝓝[>] base,
      slope (fun current => ‖coordinate (parameter current) current‖) base later < threshold := by
  obtain ⟨parameterRate, parameterAfter, parameterBefore⟩ := exists_between
    (show constant * ‖velocity‖ < threshold - frozenRate by linarith)
  obtain ⟨bound, boundAfter, boundBefore⟩ := exists_between
    (show frozenRate < threshold - parameterRate by linarith)
  have difference := eventually_right_parameter_variation_le variation derivative initialInside nearbyInside parameterAfter
  have combined := eventually_norm_slope_lt_of_frozen_norm_slope
    (curve := fun current => coordinate (parameter current) current)
    (frozen := coordinate (parameter base)) rfl (frozenBound bound boundAfter) difference
  filter_upwards [combined] with later estimate
  exact estimate.trans (by linarith)

end EulerNonuniqueness.General
