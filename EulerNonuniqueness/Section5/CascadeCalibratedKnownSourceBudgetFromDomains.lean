import EulerNonuniqueness.Section1.SharpSourceBudgetRatioChoice
import EulerNonuniqueness.Section5.CascadeTimedKnownSourceBudgetFromDomains

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_uniform_calibrated_timed_known_source_budget_of_domains
    {sharpIncoming sharpOutgoing commonIncoming commonOutgoing followerConstant : ℝ}
    (sharpIncomingNonnegative : 0 ≤ sharpIncoming) (sharpOutgoingNonnegative : 0 ≤ sharpOutgoing)
    (commonIncomingNonnegative : 0 ≤ commonIncoming) (commonOutgoingNonnegative : 0 ≤ commonOutgoing)
    (followerNonnegative : 0 ≤ followerConstant) :
    let constant := 1 + 8 * (4 * sharpOutgoing + 1) + 32 * followerConstant * (4 * commonOutgoing + 1)
    1 ≤ constant ∧
    ∀ extent magnitudeMax distanceMax coefficient : ℝ,
    1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < coefficient →
    ∃ ratioMin ≥ (2 : ℝ), ∀ scales : Scales,
    0 < scales.amplitude → ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 →
    4 < scales.ratio ^ scales.alpha →
    ∀ growth timingError : ℝ, 1 ≤ growth → 0 ≤ timingError →
    (growth + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
    ∀ sectionTime scaleRoot boundaryConstant : ℝ, 0 < scaleRoot → 0 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ {cap : ℝ} {orbit : SeparatingOrbit}
      {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant shapeRadius factor monitor : ℝ},
    threshold ≤ 1 / 2 → factor ≤ 1 / 8 →
    ∀ prepared : CascadeSourcePreparedPair cap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ (receiver : Fin count) (nonterminal : receiver.val + 1 < count),
    ∀ entry distance magnitude : Fin count → ℝ, ∀ actualTime : ℕ → ℝ,
    (∀ source : Fin count, actualTime (source.val + 1) = entry source) →
    (∀ source : Fin count, receiver.val < source.val → entry source ∈ Icc 0 path.stop) →
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
    (∀ source : Fin count, receiver.val < source.val → ∀ time ∈ Icc 0 (entry source), ∀ patch,
      prepared.trajectory.movingFamily.patchMotion.domain time source patch ⊆
        Metric.closedBall (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source)
          (extent * changed.length (source.val + 1))) →
    ∀ finish : ℝ,
    let weight := growth * changed.omega (receiver.val + 1)
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let known := 8 * prepared.mixedSelectedFinerSourcePrefixBudget receiver sharpIncoming sharpOutgoing extent coefficient
        entry distance magnitude weight finish +
      (32 * followerConstant * rho / (changed.omega (receiver.val + 1) * changed.location (receiver.val + 1) ^ 4)) *
        prepared.mixedFollowerSourcePrefixBudget receiver commonIncoming commonOutgoing extent coefficient
          entry distance magnitude weight finish
    Real.exp (weight * entry nearest) * known ≤ constant * changed.seed (receiver.val + 1) ∧
      known ≤ constant * changed.seed (receiver.val + 1) * Real.exp (-weight * entry nearest) := by
  dsimp only
  let constant := 1 + 8 * (4 * sharpOutgoing + 1) + 32 * followerConstant * (4 * commonOutgoing + 1)
  have constantOne : 1 ≤ constant := by
    have sharpNonnegative : 0 ≤ 8 * (4 * sharpOutgoing + 1) := by positivity
    have commonNonnegative : 0 ≤ 32 * followerConstant * (4 * commonOutgoing + 1) := by positivity
    dsimp only [constant]
    linarith only [sharpNonnegative, commonNonnegative]
  refine ⟨constantOne, ?_⟩
  intro extent magnitudeMax distanceMax coefficient extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  obtain ⟨sharpRatio, sharpTwo, sharpEstimates⟩ := exists_uniform_sharp_source_budget_ratio
    (outgoing := sharpOutgoing) (extent := extent) (distance := distanceMax) (neutralFactor := 1)
    sharpIncomingNonnegative magnitudeNonnegative coefficientPositive (show (0 : ℝ) ≤ 1 by norm_num)
    (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨commonRatio, commonTwo, commonEstimates⟩ := exists_uniform_sharp_source_budget_ratio
    (outgoing := commonOutgoing) (extent := extent) (distance := distanceMax) (neutralFactor := 1)
    commonIncomingNonnegative magnitudeNonnegative coefficientPositive (show (0 : ℝ) ≤ 1 by norm_num)
    (show (0 : ℝ) < 1 by norm_num)
  let ratioMin := max sharpRatio commonRatio
  have ratioTwo : 2 ≤ ratioMin := sharpTwo.trans (le_max_left _ _)
  refine ⟨ratioMin, ratioTwo, ?_⟩
  intro scales amplitudePositive ratioLarge alphaPositive alphaSmall ratioPower growth timingError growthOne
    timingErrorNonnegative ratioSeparation sectionTime scaleRoot boundaryConstant rootPositive boundaryNonnegative
  have ratioBound : 2 ≤ scales.ratio := ratioTwo.trans ratioLarge
  have coefficientBound : 1 + 8 * (4 * sharpOutgoing + 100 *
      (sharpIncoming * extent ^ 2 * magnitudeMax / (coefficient * scales.ratio ^ 2) +
        sharpOutgoing * (1 + distanceMax + 1) / scales.ratio) + 1 / scales.ratio ^ 2) +
      32 * followerConstant * (4 * commonOutgoing + 100 *
        (commonIncoming * extent ^ 2 * magnitudeMax / (coefficient * scales.ratio ^ 2) +
          commonOutgoing * (1 + distanceMax + 1) / scales.ratio) + 1 / scales.ratio ^ 2) ≤ constant := by
    have sharpBound := sharpEstimates scales.ratio ((le_max_left _ _).trans ratioLarge)
    have commonBound := commonEstimates scales.ratio ((le_max_right _ _).trans ratioLarge)
    have combined := add_le_add (mul_le_mul_of_nonneg_left sharpBound (by norm_num : (0 : ℝ) ≤ 8))
      (mul_le_mul_of_nonneg_left commonBound (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) followerNonnegative))
    simpa only [constant, add_assoc] using add_le_add_left combined 1
  filter_upwards [scales.eventually_cascade_timed_known_source_budget_of_domains amplitudePositive ratioBound alphaPositive
      alphaSmall ratioPower growthOne timingErrorNonnegative ratioSeparation sectionTime rootPositive boundaryNonnegative
      sharpIncomingNonnegative sharpOutgoingNonnegative commonIncomingNonnegative commonOutgoingNonnegative
      followerNonnegative extentOne magnitudeNonnegative distanceNonnegative coefficientPositive (show (0 : ℝ) < 1 by norm_num)]
    with frequency domainEstimate
  intro count cap orbit phase dipoleAngle threshold referenceConstant shapeRadius factor monitor thresholdSmall factorSmall
    prepared path receiver nonterminal entry distance magnitude actualTime timeIdentity entryInside nearestTiming sourceTiming
    timeOrder magnitudeBounds distanceBounds domains finish
  let changed : Scales := {scales with frequency := frequency}
  let weight := growth * changed.omega (receiver.val + 1)
  let nearest : Fin count := ⟨receiver.val + 1, nonterminal⟩
  have actual := domainEstimate count thresholdSmall factorSmall prepared path receiver nonterminal entry distance magnitude
    actualTime timeIdentity entryInside nearestTiming sourceTiming timeOrder magnitudeBounds distanceBounds domains finish
  have seedNonnegative : 0 ≤ changed.seed (receiver.val + 1) := by dsimp only [Scales.seed]; positivity
  have seedBound := mul_le_mul_of_nonneg_right coefficientBound seedNonnegative
  exact ⟨actual.1.trans seedBound, actual.2.trans (mul_le_mul_of_nonneg_right seedBound (Real.exp_pos (-weight * entry nearest)).le)⟩

end EulerNonuniqueness.Paper
