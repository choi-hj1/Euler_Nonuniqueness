import EulerNonuniqueness.Section1.AdjacentSharpSourcePrefixSeedBudget
import EulerNonuniqueness.Section1.TimedOlderSharpSourcePrefixSeedBudget
import EulerNonuniqueness.Section5.CascadeMixedSelectedFinerOriginalPrefixBudget

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000

theorem Scales.eventually_cascade_timed_sharp_prefix_seed_budget (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (alphaSmall : scales.alpha < 1)
    (ratioPower : 4 < scales.ratio ^ scales.alpha) {growth timingError : ℝ} (growthOne : 1 ≤ growth)
    (timingErrorNonnegative : 0 ≤ timingError)
    (ratioSeparation : (growth + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1))
    (sectionTime : ℝ) {incoming outgoing extent magnitudeMax distanceMax neutralFactor coefficient tailTolerance : ℝ}
    (incomingNonnegative : 0 ≤ incoming) (outgoingNonnegative : 0 ≤ outgoing)
    (extentNonnegative : 0 ≤ extent) (magnitudeNonnegative : 0 ≤ magnitudeMax)
    (distanceNonnegative : 0 ≤ distanceMax) (neutralFactorNonnegative : 0 ≤ neutralFactor)
    (coefficientPositive : 0 < coefficient) (tailPositive : 0 < tailTolerance) :
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
    Real.exp (weight * entry nearest) *
      prepared.mixedSelectedFinerSourcePrefixBudget receiver incoming outgoing extent coefficient entry distance magnitude weight finish ≤
      (4 * outgoing + 100 * (incoming * extent ^ 2 * magnitudeMax / (coefficient * changed.ratio ^ 2) +
        outgoing * (1 + distanceMax + neutralFactor) / changed.ratio) + tailTolerance / changed.ratio ^ 2) *
        changed.seed (receiver.val + 1) := by
  classical
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_timed_older_sharp_source_prefix_seed_budget ratioBound alphaPositive alphaSmall ratioPower growthOne
      timingErrorNonnegative ratioSeparation sectionTime incomingNonnegative outgoingNonnegative extentNonnegative magnitudeNonnegative
      distanceNonnegative neutralFactorNonnegative coefficientPositive tailPositive] with frequency frequencyPositive olderEstimate
  intro count cap orbit phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant
    prepared receiver nonterminal entry distance magnitude actualTime timeIdentity
  dsimp only
  intro nearestTiming sourceTiming timeOrder magnitudeBounds distanceBounds neutralBounds finish
  let changed : Scales := {scales with frequency := frequency}
  let nearest : Fin count := ⟨receiver.val + 1, nonterminal⟩
  have actualTimeNearest : actualTime (receiver.val + 2) = entry nearest := by
    simpa only [nearest, Nat.add_assoc] using timeIdentity nearest
  let weight := growth * changed.omega (receiver.val + 1)
  let neutral := fun source : Fin count => ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion (entry source) source‖
  let finer := Finset.univ.filter (fun source : Fin count => receiver.val < source.val)
  let older := finer.erase nearest
  let paperIndex := fun source : Fin count => source.val + 1
  have paperInjective : Function.Injective paperIndex := fun first second equal => Fin.ext (Nat.add_right_cancel equal)
  let magnitudeNat := Function.extend paperIndex magnitude (fun _ => 0)
  let distanceNat := Function.extend paperIndex distance (fun _ => 0)
  let neutralNat := Function.extend paperIndex neutral (fun _ => 0)
  have extendMagnitude (source : Fin count) : magnitudeNat (paperIndex source) = magnitude source := paperInjective.extend_apply _ _ _
  have extendDistance (source : Fin count) : distanceNat (paperIndex source) = distance source := paperInjective.extend_apply _ _ _
  have extendNeutral (source : Fin count) : neutralNat (paperIndex source) = neutral source := paperInjective.extend_apply _ _ _
  have finerBelow {source : Fin count} (member : source ∈ finer) : receiver.val < source.val := (Finset.mem_filter.mp member).2
  have nearestMember : nearest ∈ finer := by simp only [finer, Finset.mem_filter, Finset.mem_univ, true_and, nearest]; omega
  have olderBelow {source : Fin count} (member : source ∈ older) : receiver.val + 1 < source.val := by
    obtain ⟨different, finerMember⟩ := Finset.mem_erase.mp member
    have below := finerBelow finerMember
    have notEqual : source.val ≠ receiver.val + 1 := fun equal => different (Fin.ext equal)
    omega
  have omegaPositive := changed.omega_pos frequencyPositive (show 0 < changed.ratio by change 0 < scales.ratio; linarith) (receiver.val + 1)
  have weightBound : changed.omega (receiver.val + 1) ≤ weight := by dsimp only [weight]; nlinarith only [growthOne, omegaPositive]
  have weightPositive : 0 < weight := omegaPositive.trans_le weightBound
  let incomingTerm := fun source : Fin count => incoming * extent ^ 2 *
    (changed.circulation (paperIndex source) * changed.length (paperIndex source) ^ 2 /
      |changed.location (receiver.val + 1) - changed.location (paperIndex source)| ^ 4 *
      (1 + changed.location (receiver.val + 1) / changed.location (paperIndex source))) * magnitude source /
      (coefficient * changed.omega (paperIndex source))
  let outgoingTerm := fun source : Fin count => outgoing / changed.location (receiver.val + 1) ^ 4 * changed.circulation (paperIndex source) *
    (changed.circulation (paperIndex source) / weight ^ 2 +
      ((1 + distance source) * changed.length (paperIndex source) ^ 2 + neutral source) / weight)
  let term := fun source : Fin count => (incomingTerm source + outgoingTerm source) * Real.exp (weight * (entry nearest - entry source))
  have outgoingNonnegativeAt (source : Fin count) (member : source ∈ finer) : 0 ≤ outgoingTerm source := by
    have distanceNonnegativeAt := (distanceBounds source (finerBelow member)).1
    have circulationPositive := changed.circulation_pos frequencyPositive (show 0 < changed.ratio by change 0 < scales.ratio; linarith) (paperIndex source)
    dsimp only [outgoingTerm, neutral]
    positivity
  have literalBound : Real.exp (weight * entry nearest) *
      prepared.mixedSelectedFinerSourcePrefixBudget receiver incoming outgoing extent coefficient entry distance magnitude weight finish ≤
      ∑ source ∈ finer, term source := by
    have maskBound := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset (fun source => entry source < finish) finer)
      (fun source member _ => mul_nonneg (outgoingNonnegativeAt source member) (Real.exp_pos (-weight * entry source)).le)
    have expanded : prepared.mixedSelectedFinerSourcePrefixBudget receiver incoming outgoing extent coefficient entry distance magnitude weight finish =
        (∑ source ∈ finer, incomingTerm source * Real.exp (-weight * entry source)) +
        ∑ source ∈ finer.filter (fun source => entry source < finish), outgoingTerm source * Real.exp (-weight * entry source) := by
      dsimp only [CascadeSourcePreparedPair.mixedSelectedFinerSourcePrefixBudget, finer, incomingTerm, outgoingTerm, paperIndex, neutral]
      simp_rw [Finset.mul_sum, mul_assoc]
      congr 1
      apply Finset.sum_congr rfl
      intro source _
      ring
    rw [expanded]
    apply (mul_le_mul_of_nonneg_left (add_le_add_left maskBound _) (Real.exp_pos _).le).trans_eq
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro source _
    have exponential : Real.exp (weight * entry nearest) * Real.exp (-weight * entry source) =
        Real.exp (weight * (entry nearest - entry source)) := by rw [← Real.exp_add]; congr 1; ring
    dsimp only [term]
    calc
      _ = (incomingTerm source + outgoingTerm source) *
          (Real.exp (weight * entry nearest) * Real.exp (-weight * entry source)) := by ring
      _ = _ := by rw [exponential]
  have adjacent := changed.adjacent_sharp_source_prefix_seed_budget_le frequencyPositive
    (show 0 < changed.ratio by change 0 < scales.ratio; linarith) incomingNonnegative outgoingNonnegative extentNonnegative
    (magnitudeBounds nearest (finerBelow nearestMember)).1 (distanceBounds nearest (finerBelow nearestMember)).1
    neutralFactorNonnegative coefficientPositive (receiver.val + 1) weightBound (norm_nonneg _) (neutralBounds nearest (finerBelow nearestMember))
  have nearestBound : term nearest ≤
      (4 * outgoing + 100 * (incoming * extent ^ 2 * magnitudeMax / (coefficient * changed.ratio ^ 2) +
        outgoing * (1 + distanceMax + neutralFactor) / changed.ratio)) * changed.seed (receiver.val + 1) := by
    have seedNonnegative : 0 ≤ changed.seed (receiver.val + 1) := by dsimp only [Scales.seed]; positivity
    have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
    have actual : term nearest ≤
        (4 * outgoing + 100 * (incoming * extent ^ 2 * magnitude nearest / (coefficient * changed.ratio ^ 2) +
          outgoing * (1 + distance nearest + neutralFactor) / changed.ratio)) * changed.seed (receiver.val + 1) := by
      simpa only [term, incomingTerm, outgoingTerm, paperIndex, nearest, neutral, sub_self, mul_zero, Real.exp_zero, mul_one, Nat.add_assoc] using adjacent
    apply actual.trans
    gcongr
    · exact (magnitudeBounds nearest (finerBelow nearestMember)).2
    · exact (distanceBounds nearest (finerBelow nearestMember)).2
  have olderBound : (∑ source ∈ older, term source) ≤ tailTolerance * changed.seed (receiver.val + 1) / changed.ratio ^ 2 := by
    have olderData := olderEstimate count (receiver.val + 1) (older.image paperIndex)
      (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
          exact ⟨by dsimp only [paperIndex]; have := olderBelow currentMember; omega, by dsimp only [paperIndex]; omega⟩)
      actualTime (by simpa only [Nat.add_assoc] using nearestTiming)
      (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
          exact sourceTiming current (lt_trans (by omega) (olderBelow currentMember)))
      (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
          rw [timeIdentity current, show actualTime (receiver.val + 1 + 1) = entry nearest by simpa only [nearest, Nat.add_assoc] using timeIdentity nearest]
          exact timeOrder current (lt_trans (by omega) (olderBelow currentMember)))
      magnitudeNat distanceNat neutralNat
      (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
          rw [extendMagnitude]; exact magnitudeBounds current (lt_trans (by omega) (olderBelow currentMember)))
      (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
          rw [extendDistance]; exact distanceBounds current (lt_trans (by omega) (olderBelow currentMember)))
      (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
          rw [extendNeutral]; exact ⟨norm_nonneg _, neutralBounds current (lt_trans (by omega) (olderBelow currentMember))⟩)
    dsimp only at olderData
    rw [Finset.sum_image (fun first _ second _ equal => paperInjective equal)] at olderData
    simpa only [term, incomingTerm, outgoingTerm, extendMagnitude, extendDistance, extendNeutral, timeIdentity, actualTimeNearest,
      paperIndex, weight, nearest, Nat.add_assoc] using olderData
  have split := Finset.add_sum_erase finer term nearestMember
  have total := literalBound.trans (split.symm.trans_le (add_le_add nearestBound olderBound))
  convert total using 1
  ring

end EulerNonuniqueness.Paper
