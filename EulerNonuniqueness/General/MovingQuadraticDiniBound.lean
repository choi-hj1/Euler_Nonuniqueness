import EulerNonuniqueness.General.MovingQuadraticInteraction
import EulerNonuniqueness.General.UpperRightBootstrap

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Parameter Space : Type*}
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem moving_quadratic_interaction_norm_le
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space)
    (groupDerivative : ∀ time, HasDerivAt group ((group time).comp generator) time)
    {bound : ℝ} (boundNonnegative : 0 ≤ bound)
    (groupBound : ∀ time value, ‖group time value‖ ≤ bound * ‖value‖)
    {coefficients : Parameter → BilinearEnd Space} {admissible : Set Parameter} {constant : NNReal}
    (lipschitz : LipschitzOnWith constant coefficients admissible)
    {parameter parameterVelocity : ℝ → Parameter} {value remainder : ℝ → Space}
    {terminal speed radius errorBound : ℝ}
    (speedNonnegative : 0 ≤ speed)
    (continuous : ContinuousOn (fun current => group (-current)
      (quadraticCoordinate (coefficients (parameter current)) 1 (value current))) (Icc 0 terminal))
    (parameterDerivative : ∀ time ∈ Ico 0 terminal, HasDerivAt parameter (parameterVelocity time) time)
    (valueContinuous : ∀ time ∈ Ico 0 terminal, ContinuousAt value time)
    (inside : ∀ time ∈ Ico 0 terminal, parameter time ∈ admissible)
    (nearbyInside : ∀ time ∈ Ico 0 terminal, ∀ᶠ later in 𝓝 time, parameter later ∈ admissible)
    (frozenDerivative : ∀ time ∈ Ico 0 terminal, HasDerivAt
      (fun current => quadraticCoordinate (coefficients (parameter time)) 1 (value current))
      (generator (quadraticCoordinate (coefficients (parameter time)) 1 (value time)) + remainder time) time)
    (parameterBound : ∀ time ∈ Ico 0 terminal, ‖parameterVelocity time‖ ≤ speed)
    (valueBound : ∀ time ∈ Ico 0 terminal, ‖value time‖ ≤ radius)
    (remainderBound : ∀ time ∈ Ico 0 terminal, ‖group (-time) (remainder time)‖ ≤ errorBound) :
    ∀ time ∈ Icc 0 terminal,
      ‖group (-time) (quadraticCoordinate (coefficients (parameter time)) 1 (value time))‖ ≤
        ‖group 0 (quadraticCoordinate (coefficients (parameter 0)) 1 (value 0))‖ +
          (errorBound + bound * (constant : ℝ) * speed * radius ^ 2) * time := by
  have integrated := norm_le_linear_of_upper_right_slopes continuous (by
    intro base baseInside threshold thresholdStrict
    let excess : ℝ := (threshold - (errorBound + bound * (constant : ℝ) * speed * radius ^ 2)) /
      (2 * (bound + 1))
    have excessPositive : 0 < excess := div_pos (sub_pos.mpr thresholdStrict) (by positivity)
    let rate : ℝ := (constant : ℝ) * ‖parameterVelocity base‖ * ‖value base‖ ^ 2 + excess
    have rateStrict : (constant : ℝ) * ‖parameterVelocity base‖ * ‖value base‖ ^ 2 < rate := by
      dsimp only [rate]
      linarith
    have quadraticBound : (constant : ℝ) * ‖parameterVelocity base‖ * ‖value base‖ ^ 2 ≤
        (constant : ℝ) * speed * radius ^ 2 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (parameterBound base baseInside) constant.coe_nonneg
      · exact pow_le_pow_left₀ (norm_nonneg _) (valueBound base baseInside) 2
      · positivity
      · positivity
    have excessIdentity : excess * (2 * (bound + 1)) =
        threshold - (errorBound + bound * (constant : ℝ) * speed * radius ^ 2) := by
      exact div_mul_cancel₀ _ (by positivity)
    have strict : ‖group (-base) (remainder base)‖ + bound * rate < threshold := by
      have weightedBound := mul_le_mul_of_nonneg_left quadraticBound boundNonnegative
      have error := remainderBound base baseInside
      dsimp only [rate]
      nlinarith
    exact (eventually_moving_quadratic_interaction_norm_slope_lt group generator groupDerivative
      boundNonnegative groupBound lipschitz (parameterDerivative base baseInside)
      (valueContinuous base baseInside) (inside base baseInside) (nearbyInside base baseInside)
      (frozenDerivative base baseInside) rateStrict strict).frequently)
  intro time timeInside
  simpa only [neg_zero] using integrated time timeInside

end EulerNonuniqueness.General
