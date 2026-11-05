import EulerNonuniqueness.General.QuadraticCoefficientMetricVariation
import EulerNonuniqueness.General.QuadraticCoordinateChange

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Parameter Space : Type*}
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem eventually_moving_quadratic_coordinate_split_increment_le
    {coefficients : Parameter → BilinearEnd Space} {admissible : Set Parameter} {constant : NNReal}
    (lipschitz : LipschitzOnWith constant coefficients admissible)
    {parameter : ℝ → Parameter} {value : ℝ → Space} {base rate : ℝ} {velocity : Parameter}
    (derivative : HasDerivAt parameter velocity base) (valueContinuous : ContinuousAt value base)
    (initialInside : parameter base ∈ admissible)
    (nearbyInside : ∀ᶠ later in 𝓝 base, parameter later ∈ admissible)
    (strict : (constant : ℝ) * ‖velocity‖ * ‖value base‖ ^ 2 < rate) :
    ∀ᶠ later in 𝓝[>] base,
      ‖(quadraticCoordinate (coefficients (parameter later)) 1 (value later) -
          quadraticCoordinate (coefficients (parameter base)) 1 (value base)) -
        (quadraticCoordinate (coefficients (parameter base)) 1 (value later) -
          quadraticCoordinate (coefficients (parameter base)) 1 (value base))‖ ≤ rate * (later - base) := by
  filter_upwards [eventually_quadratic_coefficient_variation_le lipschitz derivative valueContinuous
    initialInside nearbyInside strict] with later bound
  have identity : (quadraticCoordinate (coefficients (parameter later)) 1 (value later) -
          quadraticCoordinate (coefficients (parameter base)) 1 (value base)) -
        (quadraticCoordinate (coefficients (parameter base)) 1 (value later) -
          quadraticCoordinate (coefficients (parameter base)) 1 (value base)) =
      -(coefficients (parameter later) (value later) (value later) -
        coefficients (parameter base) (value later) (value later)) := by
    simp only [quadraticCoordinate, one_div_one, one_smul]
    abel
  rw [identity, norm_neg]
  exact bound

theorem eventually_moving_quadratic_coordinate_norm_slope_lt
    {coefficients : Parameter → BilinearEnd Space} {admissible : Set Parameter} {constant : NNReal}
    (lipschitz : LipschitzOnWith constant coefficients admissible)
    {parameter : ℝ → Parameter} {value : ℝ → Space} {base threshold : ℝ}
    {parameterVelocity : Parameter} {mainVelocity : Space}
    (parameterDerivative : HasDerivAt parameter parameterVelocity base)
    (valueContinuous : ContinuousAt value base)
    (initialInside : parameter base ∈ admissible)
    (nearbyInside : ∀ᶠ later in 𝓝 base, parameter later ∈ admissible)
    (frozenDerivative : HasDerivAt
      (fun current => quadraticCoordinate (coefficients (parameter base)) 1 (value current)) mainVelocity base)
    (strict : ‖mainVelocity‖ + (constant : ℝ) * ‖parameterVelocity‖ * ‖value base‖ ^ 2 < threshold) :
    ∀ᶠ later in 𝓝[>] base,
      slope (fun current => ‖quadraticCoordinate (coefficients (parameter current)) 1 (value current)‖)
        base later < threshold := by
  obtain ⟨rate, after, before⟩ := exists_between
    (show (constant : ℝ) * ‖parameterVelocity‖ * ‖value base‖ ^ 2 < threshold - ‖mainVelocity‖ by linarith)
  have increment := eventually_moving_quadratic_coordinate_split_increment_le
    lipschitz parameterDerivative valueContinuous initialInside nearbyInside after
  exact eventually_norm_slope_lt_of_split_increment frozenDerivative increment (by linarith)

end EulerNonuniqueness.General
