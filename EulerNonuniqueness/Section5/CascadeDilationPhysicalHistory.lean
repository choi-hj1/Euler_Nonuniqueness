import EulerNonuniqueness.Section5.CascadeRelativeDilationHistory
import EulerNonuniqueness.Section6.PaperDilationForcingParts
import EulerNonuniqueness.Section4.UniversalReferenceMechanicalData

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def relativeDilationPhysicalVelocity {count : ℕ} (scales : Scales) (first second : PatchMotion count)
    (index : Fin count) (time : ℝ) : ℝ :=
  ((quadrupoleInternalDilationRate scales first index time - quadrupoleInternalDilationRate scales second index time) +
    (quadrupoleExternalDilationRate scales first index time - quadrupoleExternalDilationRate scales second index time) +
    (quadrupolePatchDilationRate scales first index time - quadrupolePatchDilationRate scales second index time)) /
      scales.length (index.val + 1) ^ 2

private theorem central_noncollision_of_small_paper_shape
    {count : ℕ} (motion : PatchMotion count) (time : ℝ) (index : Fin count)
    (small : |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4) :
    FourPointNoncollision (centrallySymmetricFourPoint (positiveHalfDiagonal motion time index)
      (negativeHalfDiagonal motion time index)) := by
  have upper := paper_shape_ratio_im_pos_of_small motion time index small
  have positiveNonzero : positiveHalfDiagonal motion time index ≠ 0 := by
    intro zero
    simpa only [zero, div_zero, Complex.zero_im, lt_self_iff_false] using upper
  have negativeNonzero : negativeHalfDiagonal motion time index ≠ 0 := by
    intro zero
    simpa only [zero, zero_div, Complex.zero_im, lt_self_iff_false] using upper
  have differenceNonzero : positiveHalfDiagonal motion time index - negativeHalfDiagonal motion time index ≠ 0 := by
    intro zero
    have equality := (sub_eq_zero.mp zero).symm
    simpa only [equality, div_self positiveNonzero, Complex.one_im, lt_self_iff_false] using upper
  have sumNonzero : positiveHalfDiagonal motion time index + negativeHalfDiagonal motion time index ≠ 0 := by
    intro zero
    have equality : negativeHalfDiagonal motion time index = -positiveHalfDiagonal motion time index :=
      eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using zero)
    simpa only [equality, neg_div, div_self positiveNonzero, Complex.neg_im, Complex.one_im, neg_zero,
      lt_self_iff_false] using upper
  exact centrallySymmetricFourPoint_noncollision positiveNonzero negativeNonzero differenceNonzero sumNonzero

theorem Scales.eventually_cascade_dilation_physical_original_history (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {scaleRoot boundaryConstant factor threshold referenceConstant : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant) :
    ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {shapeRadius monitor : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, index.val + 1 < count →
      ∀ time ∈ Icc 0 path.stop,
      (∀ current ∈ Icc 0 time, ∀ side,
        |unstableShape (cascadePairedMotion prepared side) current index| +
          |stableShape (cascadePairedMotion prepared side) current index| ≤ 1 / 4) →
      (diagonalDifference prepared.trajectory.movingFamily.patchMotion time index -
        diagonalDifference prepared.reference time index) /
          ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 =
        ∫ current in (0 : ℝ)..time,
          relativeDilationPhysicalVelocity {scales with frequency := frequency}
            prepared.trajectory.movingFamily.patchMotion prepared.reference index current := by
  filter_upwards [scales.eventually_cascade_relative_dilation_original_history amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative]
    with frequency history mechanical
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal time inside small
  rw [history prepared path index nonterminal time inside small]
  apply intervalIntegral.integral_congr
  intro current member
  rw [uIcc_of_le inside.1] at member
  let changed : Scales := {scales with frequency := frequency}
  have lengthPositive := changed.length_pos (index.val + 1)
  have safeTime : current ∈ Icc 0 path.stop := ⟨member.1, member.2.trans inside.2⟩
  have referenceInside : current ∈ Icc (0 : ℝ) 2 := ⟨member.1, by linarith [member.2, inside.2, path.stopBound]⟩
  have firstNoncollision : FourPointNoncollision
      (fun patch => patchCentroid prepared.trajectory.movingFamily.patchMotion current index patch) := by
    intro target source different
    exact norm_pos_iff.mp ((mul_pos factorPositive (changed.length_pos (index.val + 1))).trans_le
      (path.internal_centroid_gap safeTime index target source (Ne.symm different)))
  have secondNoncollision : FourPointNoncollision (fun patch => patchCentroid prepared.reference current index patch) := by
    intro target source different
    have actual := (mechanical _ prepared.referenceWitness.evolution prepared.referenceWitness.coarse
      current referenceInside index).1.internalSeparated target source different
    have actual' : changed.length (index.val + 1) / 100 ≤
        ‖patchCentroid prepared.reference current index target - patchCentroid prepared.reference current index source‖ := by
      simpa only [prepared.referenceIdentity] using actual
    exact norm_pos_iff.mp ((by positivity : 0 < changed.length (index.val + 1) / 100).trans_le actual')
  change (diagonalOddForcingRate changed prepared.trajectory.movingFamily.patchMotion index current -
    diagonalOddForcingRate changed prepared.reference index current) / changed.length (index.val + 1) ^ 2 =
    relativeDilationPhysicalVelocity changed prepared.trajectory.movingFamily.patchMotion prepared.reference index current
  rw [diagonalOddForcingRate_eq_internal_external_patch changed prepared.trajectory.movingFamily.patchMotion index current
      firstNoncollision (central_noncollision_of_small_paper_shape _ _ _ (small current member 0)),
    diagonalOddForcingRate_eq_internal_external_patch changed prepared.reference index current
      secondNoncollision (central_noncollision_of_small_paper_shape _ _ _ (small current member 1))]
  unfold relativeDilationPhysicalVelocity
  ring

end EulerNonuniqueness.Paper
