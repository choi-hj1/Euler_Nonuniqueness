import EulerNonuniqueness.Section5.CascadeTimedSharpPrefixSeedBudget
import EulerNonuniqueness.Section5.CascadeMixedCommonSharpBudgetComparison

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_timed_known_source_seed_budget (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (alphaSmall : scales.alpha < 1)
    (ratioPower : 4 < scales.ratio ^ scales.alpha) {growth timingError : ℝ} (growthOne : 1 ≤ growth)
    (timingErrorNonnegative : 0 ≤ timingError)
    (ratioSeparation : (growth + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1))
    (sectionTime : ℝ)
    {sharpIncoming sharpOutgoing commonIncoming commonOutgoing followerConstant extent magnitudeMax distanceMax
      neutralFactor coefficient tailTolerance : ℝ}
    (sharpIncomingNonnegative : 0 ≤ sharpIncoming) (sharpOutgoingNonnegative : 0 ≤ sharpOutgoing)
    (commonIncomingNonnegative : 0 ≤ commonIncoming) (commonOutgoingNonnegative : 0 ≤ commonOutgoing)
    (followerNonnegative : 0 ≤ followerConstant)
    (extentNonnegative : 0 ≤ extent) (magnitudeNonnegative : 0 ≤ magnitudeMax)
    (distanceNonnegative : 0 ≤ distanceMax) (neutralFactorNonnegative : 0 ≤ neutralFactor)
    (coefficientPositive : 0 < coefficient) (tailPositive : 0 < tailTolerance) :
    let sharpCoefficient := 4 * sharpOutgoing + 100 *
      (sharpIncoming * extent ^ 2 * magnitudeMax / (coefficient * scales.ratio ^ 2) +
        sharpOutgoing * (1 + distanceMax + neutralFactor) / scales.ratio) + tailTolerance / scales.ratio ^ 2
    let commonCoefficient := 4 * commonOutgoing + 100 *
      (commonIncoming * extent ^ 2 * magnitudeMax / (coefficient * scales.ratio ^ 2) +
        commonOutgoing * (1 + distanceMax + neutralFactor) / scales.ratio) + tailTolerance / scales.ratio ^ 2
    let constant := 1 + 8 * sharpCoefficient + 32 * followerConstant * commonCoefficient
    let roughConstant := 1 + 8 * (4 * sharpOutgoing + 100 *
      (sharpIncoming * extent ^ 2 * magnitudeMax / coefficient + sharpOutgoing * (1 + distanceMax + neutralFactor)) + tailTolerance) +
      32 * followerConstant * (4 * commonOutgoing + 100 *
        (commonIncoming * extent ^ 2 * magnitudeMax / coefficient + commonOutgoing * (1 + distanceMax + neutralFactor)) + tailTolerance)
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ {cap : ℝ} {orbit : SeparatingOrbit}
      {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ},
    ∀ prepared : CascadeSourcePreparedPair cap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ (receiver : Fin count) (nonterminal : receiver.val + 1 < count),
    ∀ entry distance magnitude : Fin count → ℝ, ∀ actualTime : ℕ → ℝ,
    (∀ source : Fin count, actualTime (source.val + 1) = entry source) →
    let changed : Scales := {scales with frequency := frequency}
    let nearest : Fin count := ⟨receiver.val + 1, nonterminal⟩
    |actualTime (receiver.val + 2) - changed.predictedTime sectionTime count (receiver.val + 2)| ≤
      timingError / changed.omega (receiver.val + 2) →
    (∀ source : Fin count, receiver.val < source.val →
      |actualTime (source.val + 1) - changed.predictedTime sectionTime count (source.val + 1)| ≤
        timingError / changed.omega (source.val + 1)) →
    (∀ source : Fin count, receiver.val < source.val → entry source ≤ entry nearest) →
    (∀ source : Fin count, receiver.val < source.val → 0 ≤ magnitude source ∧ magnitude source ≤ magnitudeMax) →
    (∀ source : Fin count, receiver.val < source.val → 0 ≤ distance source ∧ distance source ≤ distanceMax) →
    (∀ source : Fin count, receiver.val < source.val →
      ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion (entry source) source‖ ≤
        neutralFactor * changed.length (source.val + 1) ^ 2) →
    ∀ finish : ℝ,
    let weight := growth * changed.omega (receiver.val + 1)
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let known := 8 * prepared.mixedSelectedFinerSourcePrefixBudget receiver sharpIncoming sharpOutgoing extent coefficient
        entry distance magnitude weight finish +
      (32 * followerConstant * rho / (changed.omega (receiver.val + 1) * changed.location (receiver.val + 1) ^ 4)) *
        prepared.mixedFollowerSourcePrefixBudget receiver commonIncoming commonOutgoing extent coefficient
          entry distance magnitude weight finish
    Real.exp (weight * entry nearest) * known ≤ constant * changed.seed (receiver.val + 1) ∧
      known ≤ constant * changed.seed (receiver.val + 1) * Real.exp (-weight * entry nearest) ∧
      Real.exp (weight * entry nearest) * known ≤ roughConstant * changed.seed (receiver.val + 1) := by
  dsimp only
  let sharpCoefficient := 4 * sharpOutgoing + 100 *
    (sharpIncoming * extent ^ 2 * magnitudeMax / (coefficient * scales.ratio ^ 2) +
      sharpOutgoing * (1 + distanceMax + neutralFactor) / scales.ratio) + tailTolerance / scales.ratio ^ 2
  let commonCoefficient := 4 * commonOutgoing + 100 *
    (commonIncoming * extent ^ 2 * magnitudeMax / (coefficient * scales.ratio ^ 2) +
      commonOutgoing * (1 + distanceMax + neutralFactor) / scales.ratio) + tailTolerance / scales.ratio ^ 2
  let constant := 1 + 8 * sharpCoefficient + 32 * followerConstant * commonCoefficient
  let roughCoefficient := fun incoming outgoing => 4 * outgoing + 100 *
    (incoming * extent ^ 2 * magnitudeMax / coefficient + outgoing * (1 + distanceMax + neutralFactor)) + tailTolerance
  let roughConstant := 1 + 8 * roughCoefficient sharpIncoming sharpOutgoing +
    32 * followerConstant * roughCoefficient commonIncoming commonOutgoing
  have ratioPositive : 0 < scales.ratio := lt_of_lt_of_le (by norm_num) ratioBound
  have ratioOne : 1 ≤ scales.ratio := (by norm_num : (1 : ℝ) ≤ 2).trans ratioBound
  have ratioSquareOne : 1 ≤ scales.ratio ^ 2 := one_le_pow₀ ratioOne
  have roughBound (incoming outgoing : ℝ) (incomingNonnegative : 0 ≤ incoming) (outgoingNonnegative : 0 ≤ outgoing) :
      4 * outgoing + 100 * (incoming * extent ^ 2 * magnitudeMax / (coefficient * scales.ratio ^ 2) +
        outgoing * (1 + distanceMax + neutralFactor) / scales.ratio) + tailTolerance / scales.ratio ^ 2 ≤
      roughCoefficient incoming outgoing := by
    have incomingBound := div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg incomingNonnegative (sq_nonneg extent)) magnitudeNonnegative) coefficientPositive
      (le_mul_of_one_le_right coefficientPositive.le ratioSquareOne)
    have outgoingBound := div_le_self
      (mul_nonneg outgoingNonnegative (by positivity : 0 ≤ 1 + distanceMax + neutralFactor)) ratioOne
    have tailBound := div_le_self tailPositive.le ratioSquareOne
    exact add_le_add (add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add incomingBound outgoingBound)
      (by norm_num : (0 : ℝ) ≤ 100)) _) tailBound
  have constantRough : constant ≤ roughConstant := by
    have combined := add_le_add
      (mul_le_mul_of_nonneg_left (roughBound sharpIncoming sharpOutgoing sharpIncomingNonnegative sharpOutgoingNonnegative)
        (by norm_num : (0 : ℝ) ≤ 8))
      (mul_le_mul_of_nonneg_left (roughBound commonIncoming commonOutgoing commonIncomingNonnegative commonOutgoingNonnegative)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) followerNonnegative))
    simpa only [constant, roughConstant, sharpCoefficient, commonCoefficient, add_assoc] using add_le_add_left combined 1
  have commonCoefficientNonnegative : 0 ≤ commonCoefficient := by dsimp only [commonCoefficient]; positivity
  have rhoDecay := ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
    ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576)
  simp only [mul_zero, add_zero] at rhoDecay
  filter_upwards [scales.eventually_cascade_timed_sharp_prefix_seed_budget ratioBound alphaPositive alphaSmall ratioPower
      growthOne timingErrorNonnegative ratioSeparation sectionTime sharpIncomingNonnegative sharpOutgoingNonnegative
      extentNonnegative magnitudeNonnegative distanceNonnegative neutralFactorNonnegative coefficientPositive tailPositive,
    scales.eventually_cascade_timed_sharp_prefix_seed_budget ratioBound alphaPositive alphaSmall ratioPower
      growthOne timingErrorNonnegative ratioSeparation sectionTime commonIncomingNonnegative commonOutgoingNonnegative
      extentNonnegative magnitudeNonnegative distanceNonnegative neutralFactorNonnegative coefficientPositive tailPositive,
    eventually_ge_atTop (1 : ℝ), rhoDecay.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency sharpEstimate commonEstimate frequencyOne rhoSmall
  intro count cap orbit phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant
    prepared receiver nonterminal entry distance magnitude actualTime timeIdentity nearestTiming sourceTiming timeOrder
    magnitudeBounds distanceBounds neutralBounds finish
  let changed : Scales := {scales with frequency := frequency}
  let nearest : Fin count := ⟨receiver.val + 1, nonterminal⟩
  let weight := growth * changed.omega (receiver.val + 1)
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let sharpBudget := prepared.mixedSelectedFinerSourcePrefixBudget receiver sharpIncoming sharpOutgoing extent coefficient
    entry distance magnitude weight finish
  let commonSharpBudget := prepared.mixedSelectedFinerSourcePrefixBudget receiver commonIncoming commonOutgoing extent coefficient
    entry distance magnitude weight finish
  let commonBudget := prepared.mixedFollowerSourcePrefixBudget receiver commonIncoming commonOutgoing extent coefficient
    entry distance magnitude weight finish
  let returned := rho / (changed.omega (receiver.val + 1) * changed.location (receiver.val + 1) ^ 4) * commonBudget
  let known := 8 * sharpBudget + 32 * followerConstant * returned
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (receiver.val + 1)
  have weightPositive : 0 < weight := mul_pos (zero_lt_one.trans_le growthOne) omegaPositive
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
    dsimp only [rho]
    positivity
  have gainNonnegative : 0 ≤ rho / changed.frequency := div_nonneg rhoNonnegative frequencyPositive.le
  have rhoBelow : rho < 1 := by simpa only [rho, changed, mul_comm] using rhoSmall
  have gainOne : rho / changed.frequency ≤ 1 :=
    (div_le_one frequencyPositive).mpr (rhoBelow.le.trans frequencyOne)
  have seedNonnegative : 0 ≤ changed.seed (receiver.val + 1) := by dsimp only [Scales.seed]; positivity
  have sharpBound := sharpEstimate count prepared receiver nonterminal entry distance magnitude actualTime timeIdentity
    nearestTiming sourceTiming timeOrder magnitudeBounds distanceBounds neutralBounds finish
  have commonBound := commonEstimate count prepared receiver nonterminal entry distance magnitude actualTime timeIdentity
    nearestTiming sourceTiming timeOrder magnitudeBounds distanceBounds neutralBounds finish
  change Real.exp (weight * entry nearest) * sharpBudget ≤ sharpCoefficient * changed.seed (receiver.val + 1) at sharpBound
  change Real.exp (weight * entry nearest) * commonSharpBudget ≤ commonCoefficient * changed.seed (receiver.val + 1) at commonBound
  have comparison := prepared.mixed_common_sharp_budget_comparison receiver (extent := extent) (finish := finish)
    entry distance magnitude frequencyPositive
    ratioBound commonIncomingNonnegative commonOutgoingNonnegative coefficientPositive weightPositive rhoNonnegative
    (fun source below => (magnitudeBounds source below).1) (fun source below => (distanceBounds source below).1)
  have returnedBound : Real.exp (weight * entry nearest) * returned ≤ commonCoefficient * changed.seed (receiver.val + 1) := by
    calc
      _ ≤ (rho / changed.frequency) * (Real.exp (weight * entry nearest) * commonSharpBudget) := by
        convert mul_le_mul_of_nonneg_left comparison (Real.exp_pos (weight * entry nearest)).le using 1
        ring
      _ ≤ (rho / changed.frequency) * (commonCoefficient * changed.seed (receiver.val + 1)) :=
        mul_le_mul_of_nonneg_left commonBound gainNonnegative
      _ ≤ _ := mul_le_of_le_one_left (mul_nonneg commonCoefficientNonnegative seedNonnegative) gainOne
  have combined := add_le_add (mul_le_mul_of_nonneg_left sharpBound (by norm_num : (0 : ℝ) ≤ 8))
    (mul_le_mul_of_nonneg_left returnedBound (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) followerNonnegative))
  have normalized : Real.exp (weight * entry nearest) * known ≤ constant * changed.seed (receiver.val + 1) := by
    have enlarged := combined.trans (le_add_of_nonneg_right seedNonnegative)
    convert enlarged using 1 <;> dsimp only [known, constant] <;> ring
  have cancellation : Real.exp (-weight * entry nearest) * Real.exp (weight * entry nearest) = 1 := by
    rw [← Real.exp_add]
    simp only [neg_mul, neg_add_cancel, Real.exp_zero]
  have unscaled := mul_le_mul_of_nonneg_left normalized (Real.exp_pos (-weight * entry nearest)).le
  rw [← mul_assoc, cancellation, one_mul] at unscaled
  have knownIdentity : known = 8 * prepared.mixedSelectedFinerSourcePrefixBudget receiver sharpIncoming sharpOutgoing extent coefficient
      entry distance magnitude weight finish +
      (32 * followerConstant * rho / (changed.omega (receiver.val + 1) * changed.location (receiver.val + 1) ^ 4)) *
        prepared.mixedFollowerSourcePrefixBudget receiver commonIncoming commonOutgoing extent coefficient
          entry distance magnitude weight finish := by dsimp only [known, sharpBudget, returned, commonBudget]; ring
  rw [knownIdentity] at normalized unscaled
  refine ⟨normalized, ?_, normalized.trans (mul_le_mul_of_nonneg_right constantRough seedNonnegative)⟩
  calc
    _ ≤ Real.exp (-weight * entry nearest) * (constant * changed.seed (receiver.val + 1)) := unscaled
    _ = constant * changed.seed (receiver.val + 1) * Real.exp (-weight * entry nearest) := by ring

end EulerNonuniqueness.Paper
