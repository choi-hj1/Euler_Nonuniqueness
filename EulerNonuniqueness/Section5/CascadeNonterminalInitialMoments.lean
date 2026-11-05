import EulerNonuniqueness.Section5.CascadeMaterialPreparedPair
import EulerNonuniqueness.Section4.ReferenceInitialInvariants

noncomputable section

open Set
open scoped BigOperators

namespace EulerNonuniqueness.Paper.CascadeMaterialPreparedPair

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}

theorem nonterminal_initial_centroid
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (index : Fin count) (nonterminal : index.val + 1 < count) (patch : Fin 4) :
    patchCentroid prepared.trajectory.movingFamily.patchMotion 0 index patch =
      patchCentroid prepared.reference 0 index patch := by
  unfold patchCentroid
  rw [(prepared.commonInitial.1 index nonterminal patch).1]

theorem nonterminal_initial_center
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (index : Fin count) (nonterminal : index.val + 1 < count) :
    quadrupoleCenter prepared.trajectory.movingFamily.patchMotion 0 index = quadrupoleCenter prepared.reference 0 index := by
  unfold quadrupoleCenter
  congr 1
  apply Finset.sum_congr rfl
  intro patch _
  exact prepared.nonterminal_initial_centroid index nonterminal patch

theorem nonterminal_initial_invariants
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (thresholdSmall : threshold ≤ 1 / 2)
    (index : Fin count) (nonterminal : index.val + 1 < count) :
    centroidAsymmetry prepared.trajectory.movingFamily.patchMotion 0 index = 0 ∧
    diagonalDifference prepared.trajectory.movingFamily.patchMotion 0 index = scales.length (index.val + 1) ^ 2 ∧
    angularImpulse scales prepared.trajectory.movingFamily.patchMotion 0 index =
      2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2 := by
  obtain ⟨unstable, phaseLift, initial, _, evolution, _⟩ := prepared.referenceSolution
  have initialCenter := evolution.reference_initial_center_and_asymmetry (by norm_num : (0 : ℝ) ≤ 2)
    amplitudePositive frequencyPositive ratioPositive initial index
  have initialDifference := evolution.reference_initial_diagonalDifference (by norm_num : (0 : ℝ) ≤ 2)
    amplitudePositive frequencyPositive ratioPositive initial thresholdSmall index
  have initialImpulse := evolution.reference_initial_angularImpulse (by norm_num : (0 : ℝ) ≤ 2)
    amplitudePositive frequencyPositive ratioPositive initial thresholdSmall index
  have centroidEquality := prepared.nonterminal_initial_centroid index nonterminal
  have centerEquality := prepared.nonterminal_initial_center index nonterminal
  have densityEquality := cascade_initial_quadrupole_agree scales orbit sectionTime dipoleAngle
    prepared.reference prepared.trajectory.movingFamily.patchMotion prepared.commonInitial index nonterminal
  refine ⟨?_, ?_, ?_⟩
  · simpa only [centroidAsymmetry, centroidEquality] using initialCenter.2
  · simpa only [diagonalDifference, positiveHalfDiagonal, negativeHalfDiagonal, centroidEquality] using initialDifference
  · simpa only [angularImpulse, densityEquality, centerEquality] using initialImpulse

end EulerNonuniqueness.Paper.CascadeMaterialPreparedPair
