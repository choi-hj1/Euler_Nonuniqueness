import EulerNonuniqueness.General.BilinearOperatorCalculus
import EulerNonuniqueness.General.MetricSlopeComparison

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Parameter Space : Type*}
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem quadratic_coefficient_variation_norm_le
    {coefficients : Parameter → BilinearEnd Space} {admissible : Set Parameter} {constant : NNReal}
    (lipschitz : LipschitzOnWith constant coefficients admissible)
    {initial final : Parameter} (initialInside : initial ∈ admissible) (finalInside : final ∈ admissible)
    (value : Space) :
    ‖coefficients final value value - coefficients initial value value‖ ≤
      (constant : ℝ) * ‖final - initial‖ * ‖value‖ ^ 2 := by
  have differenceBound : ‖coefficients final - coefficients initial‖ ≤ (constant : ℝ) * ‖final - initial‖ := by
    simpa only [dist_eq_norm] using lipschitz.dist_le_mul final finalInside initial initialInside
  have evaluation := (coefficients final - coefficients initial).le_opNorm₂ value value
  change ‖coefficients final value value - coefficients initial value value‖ ≤ _ at evaluation
  exact evaluation.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right differenceBound (norm_nonneg value)) (norm_nonneg value)).trans_eq (by ring))

theorem eventually_quadratic_coefficient_variation_le
    {coefficients : Parameter → BilinearEnd Space} {admissible : Set Parameter} {constant : NNReal}
    (lipschitz : LipschitzOnWith constant coefficients admissible)
    {parameter : ℝ → Parameter} {value : ℝ → Space} {base rate : ℝ} {velocity : Parameter}
    (derivative : HasDerivAt parameter velocity base) (valueContinuous : ContinuousAt value base)
    (initialInside : parameter base ∈ admissible)
    (nearbyInside : ∀ᶠ later in 𝓝 base, parameter later ∈ admissible)
    (strict : (constant : ℝ) * ‖velocity‖ * ‖value base‖ ^ 2 < rate) :
    ∀ᶠ later in 𝓝[>] base,
      ‖coefficients (parameter later) (value later) (value later) -
          coefficients (parameter base) (value later) (value later)‖ ≤ rate * (later - base) := by
  have slopes : Tendsto (slope parameter base) (𝓝[>] base) (𝓝 velocity) := by
    have actual := hasDerivWithinAt_iff_tendsto_slope.mp (derivative.hasDerivWithinAt (s := Ici base))
    rwa [Ici_diff_left] at actual
  have scalarLimit : Tendsto (fun later => (constant : ℝ) * ‖slope parameter base later‖ * ‖value later‖ ^ 2)
      (𝓝[>] base) (𝓝 ((constant : ℝ) * ‖velocity‖ * ‖value base‖ ^ 2)) :=
    (tendsto_const_nhds.mul slopes.norm).mul
      ((valueContinuous.tendsto.mono_left nhdsWithin_le_nhds).norm.pow 2)
  have smallScalar := scalarLimit.eventually (eventually_lt_nhds strict)
  filter_upwards [smallScalar, nearbyInside.filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with later coefficientSmall finalInside after
  have differencePositive : 0 < later - base := sub_pos.mpr after
  have actual := quadratic_coefficient_variation_norm_le lipschitz initialInside finalInside (value later)
  have normalization : (constant : ℝ) * ‖parameter later - parameter base‖ * ‖value later‖ ^ 2 =
      ((constant : ℝ) * ‖slope parameter base later‖ * ‖value later‖ ^ 2) * (later - base) := by
    rw [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos differencePositive]
    field_simp
  exact actual.trans (normalization ▸ mul_le_mul_of_nonneg_right coefficientSmall.le differencePositive.le)

end EulerNonuniqueness.General
