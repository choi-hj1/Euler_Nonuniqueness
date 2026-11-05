import EulerNonuniqueness.General.MetricSlopeComparison
import EulerNonuniqueness.General.UpperRightBootstrap

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Parameter Space : Type*}
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem eventually_moving_coordinate_parameter_variation_le
    {coordinate : Parameter → ℝ → Space} {admissible : Set Parameter} {constant : ℝ} {weight : ℝ → ℝ}
    (variation : ∀ first ∈ admissible, ∀ second ∈ admissible, ∀ time,
      ‖coordinate first time - coordinate second time‖ ≤ constant * ‖first - second‖ * weight time)
    {parameter : ℝ → Parameter} {base rate : ℝ} {velocity : Parameter}
    (derivative : HasDerivAt parameter velocity base) (weightContinuous : ContinuousAt weight base)
    (initialInside : parameter base ∈ admissible)
    (nearbyInside : ∀ᶠ later in 𝓝 base, parameter later ∈ admissible)
    (strict : constant * ‖velocity‖ * weight base < rate) :
    ∀ᶠ later in 𝓝[>] base,
      ‖coordinate (parameter later) later - coordinate (parameter base) later‖ ≤ rate * (later - base) := by
  have slopes : Tendsto (slope parameter base) (𝓝[>] base) (𝓝 velocity) := by
    have actual := hasDerivWithinAt_iff_tendsto_slope.mp (derivative.hasDerivWithinAt (s := Ici base))
    rwa [Ici_diff_left] at actual
  have scalarLimit : Tendsto (fun later => constant * ‖slope parameter base later‖ * weight later)
      (𝓝[>] base) (𝓝 (constant * ‖velocity‖ * weight base)) :=
    (tendsto_const_nhds.mul slopes.norm).mul (weightContinuous.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [scalarLimit.eventually (eventually_lt_nhds strict),
    nearbyInside.filter_mono nhdsWithin_le_nhds, eventually_mem_nhdsWithin] with later small finalInside after
  have positive : 0 < later - base := sub_pos.mpr after
  have normalization : constant * ‖parameter later - parameter base‖ * weight later =
      (constant * ‖slope parameter base later‖ * weight later) * (later - base) := by
    rw [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos positive]
    field_simp
  exact (variation _ finalInside _ initialInside later).trans
    (normalization ▸ mul_le_mul_of_nonneg_right small.le positive.le)

theorem eventually_moving_lipschitz_coordinate_norm_slope_lt
    {coordinate : Parameter → ℝ → Space} {admissible : Set Parameter} {constant : ℝ} {weight : ℝ → ℝ}
    (variation : ∀ first ∈ admissible, ∀ second ∈ admissible, ∀ time,
      ‖coordinate first time - coordinate second time‖ ≤ constant * ‖first - second‖ * weight time)
    {parameter : ℝ → Parameter} {base threshold : ℝ} {parameterVelocity : Parameter} {mainVelocity : Space}
    (parameterDerivative : HasDerivAt parameter parameterVelocity base) (weightContinuous : ContinuousAt weight base)
    (initialInside : parameter base ∈ admissible)
    (nearbyInside : ∀ᶠ later in 𝓝 base, parameter later ∈ admissible)
    (frozenDerivative : HasDerivAt (coordinate (parameter base)) mainVelocity base)
    (strict : ‖mainVelocity‖ + constant * ‖parameterVelocity‖ * weight base < threshold) :
    ∀ᶠ later in 𝓝[>] base,
      slope (fun current => ‖coordinate (parameter current) current‖) base later < threshold := by
  obtain ⟨rate, after, before⟩ := exists_between
    (show constant * ‖parameterVelocity‖ * weight base < threshold - ‖mainVelocity‖ by linarith)
  have variationBound := eventually_moving_coordinate_parameter_variation_le variation parameterDerivative
    weightContinuous initialInside nearbyInside after
  have split : ∀ᶠ later in 𝓝[>] base,
      ‖(coordinate (parameter later) later - coordinate (parameter base) base) -
        (coordinate (parameter base) later - coordinate (parameter base) base)‖ ≤ rate * (later - base) := by
    filter_upwards [variationBound] with later bound
    convert bound using 1
    congr 1
    abel
  exact eventually_norm_slope_lt_of_split_increment frozenDerivative split (by linarith)

theorem moving_lipschitz_coordinate_norm_le
    {coordinate : Parameter → ℝ → Space} {admissible : Set Parameter} {constant : ℝ} {weight : ℝ → ℝ}
    (constantNonnegative : 0 ≤ constant)
    (variation : ∀ first ∈ admissible, ∀ second ∈ admissible, ∀ time,
      ‖coordinate first time - coordinate second time‖ ≤ constant * ‖first - second‖ * weight time)
    {parameter parameterVelocity : ℝ → Parameter} {mainVelocity : ℝ → Space}
    {terminal speed radius errorBound : ℝ}
    (speedNonnegative : 0 ≤ speed)
    (continuous : ContinuousOn (fun current => coordinate (parameter current) current) (Icc 0 terminal))
    (parameterDerivative : ∀ time ∈ Ico 0 terminal, HasDerivAt parameter (parameterVelocity time) time)
    (weightContinuous : ∀ time ∈ Ico 0 terminal, ContinuousAt weight time)
    (inside : ∀ time ∈ Ico 0 terminal, parameter time ∈ admissible)
    (nearbyInside : ∀ time ∈ Ico 0 terminal, ∀ᶠ later in 𝓝 time, parameter later ∈ admissible)
    (frozenDerivative : ∀ time ∈ Ico 0 terminal, HasDerivAt (coordinate (parameter time)) (mainVelocity time) time)
    (parameterBound : ∀ time ∈ Ico 0 terminal, ‖parameterVelocity time‖ ≤ speed)
    (weightNonnegative : ∀ time ∈ Ico 0 terminal, 0 ≤ weight time)
    (weightBound : ∀ time ∈ Ico 0 terminal, weight time ≤ radius)
    (remainderBound : ∀ time ∈ Ico 0 terminal, ‖mainVelocity time‖ ≤ errorBound) :
    ∀ time ∈ Icc 0 terminal,
      ‖coordinate (parameter time) time‖ ≤ ‖coordinate (parameter 0) 0‖ +
        (errorBound + constant * speed * radius) * time := by
  apply norm_le_linear_of_upper_right_slopes continuous
  intro base baseInside threshold thresholdStrict
  have coefficientBound : constant * ‖parameterVelocity base‖ * weight base ≤ constant * speed * radius :=
    mul_le_mul (mul_le_mul_of_nonneg_left (parameterBound base baseInside) constantNonnegative)
      (weightBound base baseInside) (weightNonnegative base baseInside) (mul_nonneg constantNonnegative speedNonnegative)
  have strict : ‖mainVelocity base‖ + constant * ‖parameterVelocity base‖ * weight base < threshold :=
    (add_le_add (remainderBound base baseInside) coefficientBound).trans_lt thresholdStrict
  exact (eventually_moving_lipschitz_coordinate_norm_slope_lt variation (parameterDerivative base baseInside)
    (weightContinuous base baseInside) (inside base baseInside) (nearbyInside base baseInside)
    (frozenDerivative base baseInside) strict).frequently

end EulerNonuniqueness.General
