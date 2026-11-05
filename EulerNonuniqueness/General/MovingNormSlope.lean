import EulerNonuniqueness.General.MovingLipschitzCoordinate

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space Parameter : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

theorem norm_slope_le_frozen_norm_slope_of_difference
    (curve frozen : ℝ → Space) {base later rate : ℝ}
    (after : base < later) (sameBase : curve base = frozen base)
    (difference : ‖curve later - frozen later‖ ≤ rate * (later - base)) :
    slope (fun current => ‖curve current‖) base later ≤
      slope (fun current => ‖frozen current‖) base later + rate := by
  have positive : 0 < later - base := sub_pos.mpr after
  have triangle := (norm_sub_norm_le (curve later) (frozen later)).trans difference
  simp only [slope_def_field, sameBase]
  apply (div_le_iff₀ positive).mpr
  rw [add_mul, div_mul_cancel₀ _ positive.ne']
  linarith

theorem eventually_norm_slope_lt_of_frozen_norm_slope
    {curve frozen : ℝ → Space} {base bound rate : ℝ}
    (sameBase : curve base = frozen base)
    (frozenBound : ∀ᶠ later in 𝓝[>] base,
      slope (fun current => ‖frozen current‖) base later < bound)
    (difference : ∀ᶠ later in 𝓝[>] base,
      ‖curve later - frozen later‖ ≤ rate * (later - base)) :
    ∀ᶠ later in 𝓝[>] base, slope (fun current => ‖curve current‖) base later < bound + rate := by
  filter_upwards [frozenBound, difference, eventually_mem_nhdsWithin] with later boundActual differenceActual after
  exact (norm_slope_le_frozen_norm_slope_of_difference curve frozen after sameBase differenceActual).trans_lt
    (add_lt_add_right boundActual rate)

theorem eventually_moving_norm_slope_lt_of_frozen_upper_bound
    {coordinate : Parameter → ℝ → Space} {admissible : Set Parameter} {constant : ℝ} {weight : ℝ → ℝ}
    (variation : ∀ first ∈ admissible, ∀ second ∈ admissible, ∀ time,
      ‖coordinate first time - coordinate second time‖ ≤ constant * ‖first - second‖ * weight time)
    {parameter : ℝ → Parameter} {base frozenRate threshold : ℝ} {velocity : Parameter}
    (derivative : HasDerivAt parameter velocity base) (weightContinuous : ContinuousAt weight base)
    (initialInside : parameter base ∈ admissible)
    (nearbyInside : ∀ᶠ later in 𝓝 base, parameter later ∈ admissible)
    (frozenBound : ∀ bound : ℝ, frozenRate < bound → ∀ᶠ later in 𝓝[>] base,
      slope (fun current => ‖coordinate (parameter base) current‖) base later < bound)
    (strict : frozenRate + constant * ‖velocity‖ * weight base < threshold) :
    ∀ᶠ later in 𝓝[>] base,
      slope (fun current => ‖coordinate (parameter current) current‖) base later < threshold := by
  obtain ⟨parameterRate, parameterAfter, parameterBefore⟩ := exists_between
    (show constant * ‖velocity‖ * weight base < threshold - frozenRate by linarith)
  obtain ⟨bound, boundAfter, boundBefore⟩ := exists_between
    (show frozenRate < threshold - parameterRate by linarith)
  have difference := eventually_moving_coordinate_parameter_variation_le variation derivative weightContinuous
    initialInside nearbyInside parameterAfter
  have combined := eventually_norm_slope_lt_of_frozen_norm_slope
    (curve := fun current => coordinate (parameter current) current)
    (frozen := coordinate (parameter base)) rfl (frozenBound bound boundAfter) difference
  filter_upwards [combined] with later estimate
  exact estimate.trans (by linarith)

end EulerNonuniqueness.General
