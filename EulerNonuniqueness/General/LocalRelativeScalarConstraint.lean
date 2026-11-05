import EulerNonuniqueness.General.RelativeScalarConstraint
import EulerNonuniqueness.General.RelativeDecompositionBound
import EulerNonuniqueness.Section3.LocalLipschitzCalculus

namespace EulerNonuniqueness.General

noncomputable section

open Filter Metric
open scoped Topology

set_option maxHeartbeats 1000000

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem exists_relative_mean_ball
    (projection transverseProjection : Space →L[ℝ] Space) (radial : Space)
    (mean coefficient constraint : Space → ℝ) (remainder : Space → Space → ℝ)
    {value : ℝ} (valuePositive : 0 < value)
    (relativeRemainder : ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final first second : Space,
      ‖initial‖ + (‖first‖ + ‖second‖) ≤ radius → ‖final‖ + (‖first‖ + ‖second‖) ≤ radius →
      |remainder initial first - remainder final second| ≤ constant *
        ((‖first‖ + ‖second‖) * ‖first - second‖ + ‖initial - final‖ * ‖second‖ ^ 2))
    (absoluteAbsorption : ∃ radius > 0, ∃ constant ≥ 0, ∀ state : Space,
      ‖projection state‖ + ‖state - projection state‖ ≤ radius → constraint state = value →
      ‖state - projection state‖ ≤ 2 * ‖transverseProjection (state - projection state)‖ ∧
      |mean (state - projection state)| ≤ constant * ‖transverseProjection (state - projection state)‖ ^ 2)
    (coefficientRegular : LipschitzNear coefficient (0 : Space))
    (coefficientNeutral : ∀ state, coefficient (projection state) = coefficient state)
    (positiveCoefficient : ∀ᶠ state in 𝓝 (0 : Space), value ≤ coefficient state)
    (meanIdentity : ∀ᶠ state in 𝓝 (0 : Space), constraint state - value =
      coefficient state * mean (state - projection state) + remainder (projection state) (state - projection state))
    (decompositionHypothesis : ∀ state : Space, state - projection state =
      transverseProjection (state - projection state) + mean (state - projection state) • radial) :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      constraint initial = value → constraint final = value →
      let initialRelative := initial - projection initial
      let finalRelative := final - projection final
      let first := transverseProjection initialRelative
      let second := transverseProjection finalRelative
      |mean initialRelative - mean finalRelative| ≤ constant *
        ((‖first‖ + ‖second‖) * ‖first - second‖ +
          ‖projection initial - projection final‖ * ‖second‖ ^ 2) := by
  obtain ⟨rawRadius, rawPositive, rawConstant, rawNonnegative, rawBound⟩ :=
    relativeRemainder
  obtain ⟨absorptionRadius, absorptionPositive, absorptionConstant, absorptionNonnegative, absorption⟩ :=
    absoluteAbsorption
  obtain ⟨coefficientLip, coefficientDomain, coefficientNearby, coefficientLipschitz⟩ :=
    coefficientRegular
  let bound := 1 + 4 * rawConstant + absorptionConstant + (coefficientLip : ℝ)
  have coefficientNonnegative := coefficientLip.coe_nonneg
  have boundNonnegative : 0 ≤ bound := by dsimp only [bound]; positivity
  have rawLarge : 4 * rawConstant ≤ bound := by dsimp only [bound]; linarith
  have absorptionLarge : absorptionConstant ≤ bound := by dsimp only [bound]; linarith
  have coefficientLarge : (coefficientLip : ℝ) ≤ bound := by dsimp only [bound]; linarith
  let relativeLinear : Space →L[ℝ] Space :=
    ContinuousLinearMap.id ℝ Space - projection
  have relativeApply (state : Space) : relativeLinear state = state - projection state := rfl
  have smallWeighted (linear : Space →L[ℝ] Space)
      (factor threshold : ℝ) (positive : 0 < threshold) :
      ∀ᶠ state in 𝓝 (0 : Space), factor * ‖linear state‖ < threshold := by
    have continuous : ContinuousAt (fun state : Space => factor * ‖linear state‖) 0 :=
      continuousAt_const.mul linear.continuous.continuousAt.norm
    exact continuous.eventually (gt_mem_nhds (by simpa only [map_zero, norm_zero, mul_zero] using positive))
  let sizeRadius := min rawRadius absorptionRadius
  have sizePositive : 0 < sizeRadius := lt_min rawPositive absorptionPositive
  have neutralSmall := smallWeighted projection 1 (sizeRadius / 4) (by positivity)
  have relativeSmall := smallWeighted relativeLinear 1 (sizeRadius / 4) (by positivity)
  have budgetSmall := smallWeighted (transverseProjection.comp relativeLinear)
    (bound * ‖radial‖) (value / 4) (by positivity)
  have neutralLimit : Tendsto projection (𝓝 (0 : Space)) (𝓝 0) := by
    simpa only [map_zero] using projection.continuous.tendsto (0 : Space)
  have combined : {state | projection state ∈ coefficientDomain ∧
      ‖projection state‖ < sizeRadius / 4 ∧ ‖relativeLinear state‖ < sizeRadius / 4 ∧
      (bound * ‖radial‖) * ‖transverseProjection (relativeLinear state)‖ < value / 4 ∧
      value ≤ coefficient state ∧
      constraint state - value = coefficient state *
        mean (relativeLinear state) + remainder (projection state) (relativeLinear state)}
      ∈ 𝓝 (0 : Space) := by
    filter_upwards [neutralLimit.eventually coefficientNearby, neutralSmall, relativeSmall, budgetSmall,
      positiveCoefficient, meanIdentity]
      with state member neutralBound relativeBound budget positive identity
    exact ⟨member, by simpa only [one_mul] using neutralBound, by simpa only [one_mul] using relativeBound,
      budget, positive, identity⟩
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp combined
  refine ⟨radius, positive, (2 / value) * (bound ^ 2 + bound), by positivity, ?_⟩
  intro initial final initialInside finalInside initialArea finalArea
  obtain ⟨initialMember, initialNeutral, initialRelative, initialBudget, initialCoefficient, initialIdentity⟩ := contained initialInside
  obtain ⟨finalMember, finalNeutral, finalRelative, finalBudget, _, finalIdentity⟩ := contained finalInside
  let first := relativeLinear initial
  let second := relativeLinear final
  have initialAbsorption : ‖projection initial‖ + ‖first‖ ≤ absorptionRadius := by
    have small : sizeRadius ≤ absorptionRadius := min_le_right _ _
    dsimp only [first]
    linarith
  have finalAbsorption : ‖projection final‖ + ‖second‖ ≤ absorptionRadius := by
    have small : sizeRadius ≤ absorptionRadius := min_le_right _ _
    dsimp only [second]
    linarith
  obtain ⟨firstBound, _⟩ := absorption initial initialAbsorption initialArea
  obtain ⟨secondBound, finalMean⟩ := absorption final finalAbsorption finalArea
  have decomposition := decompositionHypothesis
  have relativeDifference := EulerNonuniqueness.General.norm_sub_le_of_scalar_decompositions
    first second (transverseProjection first) (transverseProjection second) radial
    (mean first) (mean second) (decomposition initial) (decomposition final)
  have initialDomain : ‖projection initial‖ + (‖first‖ + ‖second‖) ≤ rawRadius := by
    have small : sizeRadius ≤ rawRadius := min_le_left _ _
    dsimp only [first, second]
    linarith
  have finalDomain : ‖projection final‖ + (‖first‖ + ‖second‖) ≤ rawRadius := by
    have small : sizeRadius ≤ rawRadius := min_le_left _ _
    dsimp only [first, second]
    linarith
  have errorEstimate := rawBound (projection initial) (projection final)
    first second initialDomain finalDomain
  have errors : |remainder (projection initial) first -
      remainder (projection final) second| ≤ bound *
      ((‖transverseProjection first‖ + ‖transverseProjection second‖) *
        (‖transverseProjection first - transverseProjection second‖ +
          ‖radial‖ * |mean first - mean second|) +
        ‖projection initial - projection final‖ * ‖transverseProjection second‖ ^ 2) := by
    have firstSize : ‖first‖ ≤ 2 * ‖transverseProjection first‖ := firstBound
    have secondSize : ‖second‖ ≤ 2 * ‖transverseProjection second‖ := secondBound
    apply errorEstimate.trans
    have nonnegative := norm_nonneg (projection initial - projection final)
    have squareBound := pow_le_pow_left₀ (norm_nonneg second) secondSize 2
    have productBound := mul_le_mul (add_le_add firstSize secondSize) relativeDifference (norm_nonneg _) (by positivity)
    have rawEstimate := mul_le_mul_of_nonneg_left (add_le_add productBound
      (mul_le_mul_of_nonneg_left squareBound nonnegative)) rawNonnegative
    have enlarge := mul_le_mul_of_nonneg_right rawLarge (show 0 ≤
      (‖transverseProjection first‖ + ‖transverseProjection second‖) *
        (‖transverseProjection first - transverseProjection second‖ +
          ‖radial‖ * |mean first - mean second|) +
        ‖projection initial - projection final‖ * ‖transverseProjection second‖ ^ 2 by positivity)
    have extraNonnegative : 0 ≤ rawConstant *
        (‖transverseProjection first‖ + ‖transverseProjection second‖) *
        (‖transverseProjection first - transverseProjection second‖ +
          ‖radial‖ * |mean first - mean second|) := by positivity
    nlinarith only [rawEstimate, enlarge, extraNonnegative]
  have coefficients : |coefficient initial - coefficient final| ≤
      bound * ‖projection initial - projection final‖ := by
    have estimate := coefficientLipschitz.norm_sub_le initialMember finalMember
    rw [coefficientNeutral, coefficientNeutral] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right coefficientLarge (norm_nonneg _))
  have initialConstraint : coefficient initial * mean first +
      remainder (projection initial) first = 0 := by
    rw [initialArea, sub_self] at initialIdentity
    exact initialIdentity.symm
  have finalConstraint : coefficient final * mean second +
      remainder (projection final) second = 0 := by
    rw [finalArea, sub_self] at finalIdentity
    exact finalIdentity.symm
  have small : bound * (‖transverseProjection first‖ + ‖transverseProjection second‖) *
      ‖radial‖ ≤ value / 2 := by
    dsimp only [first, second]
    nlinarith only [initialBudget, finalBudget]
  have result := EulerNonuniqueness.General.abs_mean_difference_of_relative_constraint valuePositive boundNonnegative
    (by positivity) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) initialCoefficient coefficients
    initialConstraint finalConstraint
    (finalMean.trans (mul_le_mul_of_nonneg_right absorptionLarge (sq_nonneg _))) errors small
  apply result.trans
  dsimp only [first, second, relativeLinear, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  have coefficientBound : bound ≤ bound ^ 2 + bound := by nlinarith [sq_nonneg bound]
  have enlarge := mul_le_mul_of_nonneg_right coefficientBound (show 0 ≤
    (‖transverseProjection (initial - projection initial)‖ +
      ‖transverseProjection (final - projection final)‖) *
      ‖transverseProjection (initial - projection initial) -
        transverseProjection (final - projection final)‖ by positivity)
  nlinarith only [mul_le_mul_of_nonneg_left enlarge (show 0 ≤ 2 / value by positivity)]

end

end EulerNonuniqueness.General

