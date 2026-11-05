import EulerNonuniqueness.General.MovingQuadraticCoordinateSlope
import EulerNonuniqueness.General.OperatorWeightedSplitIncrement
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Parameter Space : Type*}
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem eventually_moving_quadratic_interaction_norm_slope_lt
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space)
    (groupDerivative : ∀ time, HasDerivAt group ((group time).comp generator) time)
    {bound : ℝ} (boundNonnegative : 0 ≤ bound)
    (groupBound : ∀ time value, ‖group time value‖ ≤ bound * ‖value‖)
    {coefficients : Parameter → BilinearEnd Space} {admissible : Set Parameter} {constant : NNReal}
    (lipschitz : LipschitzOnWith constant coefficients admissible)
    {parameter : ℝ → Parameter} {value : ℝ → Space} {base rate threshold : ℝ}
    {parameterVelocity : Parameter} {remainder : Space}
    (parameterDerivative : HasDerivAt parameter parameterVelocity base)
    (valueContinuous : ContinuousAt value base)
    (initialInside : parameter base ∈ admissible)
    (nearbyInside : ∀ᶠ later in 𝓝 base, parameter later ∈ admissible)
    (frozenDerivative : HasDerivAt
      (fun current => quadraticCoordinate (coefficients (parameter base)) 1 (value current))
      (generator (quadraticCoordinate (coefficients (parameter base)) 1 (value base)) + remainder) base)
    (rateStrict : (constant : ℝ) * ‖parameterVelocity‖ * ‖value base‖ ^ 2 < rate)
    (strict : ‖group (-base) remainder‖ + bound * rate < threshold) :
    ∀ᶠ later in 𝓝[>] base,
      slope (fun current => ‖group (-current)
        (quadraticCoordinate (coefficients (parameter current)) 1 (value current))‖) base later < threshold := by
  have inverseDerivative : HasDerivAt (fun current => group (-current))
      (-((group (-base)).comp generator)) base := by
    have inner : HasDerivAt (fun current : ℝ => -current) (-1) base := by
      simpa only [id_eq] using (hasDerivAt_id base).neg
    simpa only [neg_one_smul] using (groupDerivative (-base)).scomp base inner
  have mainDerivative : HasDerivAt (fun current => group (-current)
      (quadraticCoordinate (coefficients (parameter base)) 1 (value current)))
      (group (-base) remainder) base := by
    have actual := inverseDerivative.clm_apply frozenDerivative
    convert actual using 1
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, map_add]
    abel
  have increment := eventually_moving_quadratic_coordinate_split_increment_le
    lipschitz parameterDerivative valueContinuous initialInside nearbyInside rateStrict
  have weightedIncrement : ∀ᶠ later in 𝓝[>] base,
      ‖(group (-later) (quadraticCoordinate (coefficients (parameter later)) 1 (value later)) -
          group (-base) (quadraticCoordinate (coefficients (parameter base)) 1 (value base))) -
        (group (-later) (quadraticCoordinate (coefficients (parameter base)) 1 (value later)) -
          group (-base) (quadraticCoordinate (coefficients (parameter base)) 1 (value base)))‖ ≤
        (bound * rate) * (later - base) := by
    filter_upwards [increment] with later errorBound
    exact operator_weighted_split_increment_norm_le (fun current => group (-current))
      (fun current => quadraticCoordinate (coefficients (parameter current)) 1 (value current))
      (fun current => quadraticCoordinate (coefficients (parameter base)) 1 (value current))
      boundNonnegative (fun current point => groupBound (-current) point) rfl errorBound
  exact eventually_norm_slope_lt_of_split_increment mainDerivative weightedIncrement strict

end EulerNonuniqueness.General
