import EulerNonuniqueness.Section5.CascadeTimedKnownSourceSeedBudget
import EulerNonuniqueness.Section6.SourcePacketBoundedRadiusNeutralSmall

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_timed_known_source_budget_of_domains (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (alphaSmall : scales.alpha < 1)
    (ratioPower : 4 < scales.ratio ^ scales.alpha) {growth timingError : ℝ} (growthOne : 1 ≤ growth)
    (timingErrorNonnegative : 0 ≤ timingError)
    (ratioSeparation : (growth + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1))
    (sectionTime : ℝ) {scaleRoot boundaryConstant : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    {sharpIncoming sharpOutgoing commonIncoming commonOutgoing followerConstant extent magnitudeMax distanceMax
      coefficient tailTolerance : ℝ}
    (sharpIncomingNonnegative : 0 ≤ sharpIncoming) (sharpOutgoingNonnegative : 0 ≤ sharpOutgoing)
    (commonIncomingNonnegative : 0 ≤ commonIncoming) (commonOutgoingNonnegative : 0 ≤ commonOutgoing)
    (followerNonnegative : 0 ≤ followerConstant) (extentOne : 1 ≤ extent)
    (magnitudeNonnegative : 0 ≤ magnitudeMax) (distanceNonnegative : 0 ≤ distanceMax)
    (coefficientPositive : 0 < coefficient) (tailPositive : 0 < tailTolerance) :
    let sharpCoefficient := 4 * sharpOutgoing + 100 *
      (sharpIncoming * extent ^ 2 * magnitudeMax / (coefficient * scales.ratio ^ 2) +
        sharpOutgoing * (1 + distanceMax + 1) / scales.ratio) + tailTolerance / scales.ratio ^ 2
    let commonCoefficient := 4 * commonOutgoing + 100 *
      (commonIncoming * extent ^ 2 * magnitudeMax / (coefficient * scales.ratio ^ 2) +
        commonOutgoing * (1 + distanceMax + 1) / scales.ratio) + tailTolerance / scales.ratio ^ 2
    let constant := 1 + 8 * sharpCoefficient + 32 * followerConstant * commonCoefficient
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
  have extentPositive : 0 < extent := zero_lt_one.trans_le extentOne
  filter_upwards [scales.eventually_cascade_timed_known_source_seed_budget ratioBound alphaPositive alphaSmall ratioPower
      growthOne timingErrorNonnegative ratioSeparation sectionTime sharpIncomingNonnegative sharpOutgoingNonnegative
      commonIncomingNonnegative commonOutgoingNonnegative followerNonnegative extentPositive.le magnitudeNonnegative
      distanceNonnegative (show (0 : ℝ) ≤ 1 by norm_num) coefficientPositive tailPositive,
    scales.eventually_bounded_radius_source_neutral_small amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative extentPositive (show (0 : ℝ) < 1 by norm_num)]
    with frequency knownEstimate neutralEstimate
  intro count cap orbit phase dipoleAngle threshold referenceConstant shapeRadius factor monitor thresholdSmall factorSmall
    prepared path receiver nonterminal entry distance magnitude actualTime timeIdentity entryInside nearestTiming sourceTiming
    timeOrder magnitudeBounds distanceBounds domains finish
  have neutralBounds (source : Fin count) (below : receiver.val < source.val) :
      ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion (entry source) source‖ ≤
        (1 : ℝ) * ({scales with frequency := frequency} : Scales).length (source.val + 1) ^ 2 := by
    exact neutralEstimate prepared.toCascadeMaterialPreparedPair path thresholdSmall factorSmall source (entry source)
      (entryInside source below).1 (entryInside source below).2 (domains source below) (entry source)
      ⟨(entryInside source below).1, le_rfl⟩
  have actual := knownEstimate count prepared receiver nonterminal entry distance magnitude actualTime timeIdentity
    nearestTiming sourceTiming timeOrder magnitudeBounds distanceBounds neutralBounds finish
  exact ⟨actual.1, actual.2.1⟩

end EulerNonuniqueness.Paper
