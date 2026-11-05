import EulerNonuniqueness.General.ScaledFiberRelativeQuadratic
import EulerNonuniqueness.Section3.LocalLipschitzCalculus

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space] [NormedAddCommGroup Target]

theorem exists_scaled_fiber_relative_quadratic_ball
    (projection : Space →L[ℝ] Space) (coordinates : Space → Space →L[ℝ] Space)
    (remainder : Space → Space → Target)
    (coordinateRegular : LipschitzNear coordinates (0 : Space))
    {rawRadius rawConstant : ℝ} (rawPositive : 0 < rawRadius) (rawNonnegative : 0 ≤ rawConstant)
    (rawBound : ∀ initialBase finalBase initialIncrement finalIncrement : Space,
      ‖initialBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ rawRadius →
      ‖finalBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ rawRadius →
      ‖remainder initialBase initialIncrement - remainder finalBase finalIncrement‖ ≤ rawConstant *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 2)) :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final first second : Space,
      ‖initial‖ + (‖first‖ + ‖second‖) ≤ radius →
      ‖final‖ + (‖first‖ + ‖second‖) ≤ radius →
      ‖remainder (projection initial) (coordinates initial first) -
        remainder (projection final) (coordinates final second)‖ ≤ constant *
        ((‖first‖ + ‖second‖) * ‖first - second‖ + ‖initial - final‖ * ‖second‖ ^ 2) := by
  obtain ⟨coordinateBound, coordinateNonnegative, coordinateEstimate⟩ :=
    exists_eventually_norm_bound coordinateRegular.continuousAt
  obtain ⟨lip, domain, nearby, lipschitz⟩ := coordinateRegular
  have combined : {state | state ∈ domain ∧ ‖coordinates state‖ ≤ coordinateBound} ∈ 𝓝 (0 : Space) := by
    filter_upwards [nearby, coordinateEstimate] with state member bound
    exact ⟨member, bound⟩
  obtain ⟨neighborhoodRadius, neighborhoodPositive, contained⟩ := Metric.mem_nhds_iff.mp combined
  let bound := 1 + coordinateBound + (lip : ℝ) + ‖projection‖
  have lipNonnegative := lip.coe_nonneg
  have projectionNonnegative := norm_nonneg projection
  have boundLarge : 1 ≤ bound := by dsimp only [bound]; linarith
  have boundPositive : 0 < bound := lt_of_lt_of_le (by norm_num) boundLarge
  have coordinateLarge : coordinateBound ≤ bound := by dsimp only [bound]; linarith
  have lipLarge : (lip : ℝ) ≤ bound := by dsimp only [bound]; linarith
  have projectionLarge : ‖projection‖ ≤ bound := by dsimp only [bound]; linarith
  let radius := min (neighborhoodRadius / 2) (rawRadius / (4 * bound))
  have positive : 0 < radius := lt_min (by positivity) (by positivity)
  have scaledRadius : 4 * bound * radius ≤ rawRadius := by
    have small : radius ≤ rawRadius / (4 * bound) := min_le_right _ _
    have actual := (le_div_iff₀ (by positivity : 0 < 4 * bound)).mp small
    nlinarith
  refine ⟨radius, positive, 3 * rawConstant * bound ^ 3, by positivity, ?_⟩
  intro initial final first second initialInside finalInside
  have stateInside (state : Space) (inside : ‖state‖ + (‖first‖ + ‖second‖) ≤ radius) :
      state ∈ domain ∧ ‖coordinates state‖ ≤ bound := by
    have ballInside : state ∈ ball (0 : Space) neighborhoodRadius := by
      apply mem_ball_zero_iff.mpr
      have smaller : radius ≤ neighborhoodRadius / 2 := min_le_left _ _
      linarith [norm_nonneg first, norm_nonneg second]
    obtain ⟨member, estimate⟩ := contained ballInside
    exact ⟨member, estimate.trans coordinateLarge⟩
  obtain ⟨initialMember, initialNorm⟩ := stateInside initial initialInside
  obtain ⟨finalMember, finalNorm⟩ := stateInside final finalInside
  have baseBound (state : Space) : ‖projection state‖ ≤ bound * ‖state‖ :=
    (projection.le_opNorm state).trans (mul_le_mul_of_nonneg_right projectionLarge (norm_nonneg _))
  have imageBound (state : Space) (stateNorm : ‖coordinates state‖ ≤ bound) (vector : Space) :
      ‖coordinates state vector‖ ≤ bound * ‖vector‖ :=
    ((coordinates state).le_opNorm vector).trans (mul_le_mul_of_nonneg_right stateNorm (norm_nonneg _))
  have initialDomain : ‖projection initial‖ +
      (‖coordinates initial first‖ + ‖coordinates initial second‖) ≤ rawRadius := by
    have scaled := mul_le_mul_of_nonneg_left initialInside boundPositive.le
    nlinarith [baseBound initial, imageBound initial initialNorm first,
      imageBound initial initialNorm second, mul_nonneg boundPositive.le positive.le]
  have parameterInitial : ‖projection initial‖ +
      (‖coordinates initial second‖ + ‖coordinates final second‖) ≤ rawRadius := by
    have scaled := mul_le_mul_of_nonneg_left initialInside boundPositive.le
    nlinarith [baseBound initial, imageBound initial initialNorm second,
      imageBound final finalNorm second, mul_nonneg boundPositive.le (norm_nonneg first),
      mul_nonneg boundPositive.le (norm_nonneg initial)]
  have parameterFinal : ‖projection final‖ +
      (‖coordinates initial second‖ + ‖coordinates final second‖) ≤ rawRadius := by
    have scaled := mul_le_mul_of_nonneg_left finalInside boundPositive.le
    nlinarith [baseBound final, imageBound initial initialNorm second,
      imageBound final finalNorm second, mul_nonneg boundPositive.le (norm_nonneg first),
      mul_nonneg boundPositive.le (norm_nonneg final)]
  have incrementEstimate := rawBound (projection initial) (projection initial)
    (coordinates initial first) (coordinates initial second) initialDomain initialDomain
  have parameterEstimate := rawBound (projection initial) (projection final)
    (coordinates initial second) (coordinates final second) parameterInitial parameterFinal
  have coordinateDifference : ‖coordinates initial - coordinates final‖ ≤ bound * ‖initial - final‖ :=
    (lipschitz.norm_sub_le initialMember finalMember).trans
      (mul_le_mul_of_nonneg_right lipLarge (norm_nonneg _))
  have projectionDifference : ‖projection initial - projection final‖ ≤ bound * ‖initial - final‖ := by
    simpa only [map_sub] using baseBound (initial - final)
  apply norm_scaled_fiber_relative_quadratic_le (coordinates initial) (coordinates final) first second
    (remainder (projection initial) (coordinates initial first))
    (remainder (projection initial) (coordinates initial second))
    (remainder (projection final) (coordinates final second))
    rawNonnegative boundLarge (norm_nonneg _) initialNorm finalNorm coordinateDifference
  · simpa only [sub_self, norm_zero, zero_mul, add_zero, mul_assoc] using incrementEstimate
  · exact parameterEstimate.trans (mul_le_mul_of_nonneg_left
      (add_le_add_left (mul_le_mul_of_nonneg_right projectionDifference (sq_nonneg _)) _) rawNonnegative)

end

end EulerNonuniqueness.General
