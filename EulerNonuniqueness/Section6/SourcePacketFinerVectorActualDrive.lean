import EulerNonuniqueness.Section6.SourcePacketFinerVectorSeedTail
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect
import EulerNonuniqueness.Section4.PaperCoarseUpperBranch

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.eventually_actual_finer_source_vector_seed_bound (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (ratioPower : 4 < scales.ratio ^ scales.alpha) {tolerance : ℝ} (tolerancePositive : 0 < tolerance)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop, ∀ receiver : Fin count,
      let changed : Scales := {scales with frequency := frequency}
      ‖∑ source ∈ Finset.univ.filter (fun source : Fin count => receiver.val + 2 ≤ source.val),
        relativeBlockSourceShapeInput changed prepared.trajectory.movingFamily.patchMotion prepared.reference receiver source time‖ ≤
        tolerance * changed.seed (receiver.val + 1) := by
  obtain ⟨radius, radiusPositive, bounds⟩ := scales.exists_uniform_actual_finer_source_vector_seed_tail
    amplitudePositive ratioBound alphaPositive ratioPower tolerancePositive orbit sectionTime
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  have smallPositive : 0 < min radius (1 / 4 : ℝ) := lt_min radiusPositive (by norm_num)
  filter_upwards [bounds, scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive
    referenceNonnegative smallPositive] with frequency actual sharp
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver
  dsimp only
  have defect := sharp prepared time ⟨inside.1, inside.2.trans path.stopBound⟩ receiver
  have shapeSmall : |unstableShape prepared.reference time receiver| + |stableShape prepared.reference time receiver| ≤
      min radius (1 / 4 : ℝ) := by
    linarith only [defect, abs_nonneg (diagonalDifference prepared.reference time receiver /
      ({scales with frequency := frequency} : Scales).length (receiver.val + 1) ^ 2 - 1)]
  have upper := paper_shape_ratio_im_pos_of_small prepared.reference time receiver
    (shapeSmall.trans (min_le_right _ _))
  have positiveNonzero : positiveHalfDiagonal prepared.reference time receiver ≠ 0 := by
    intro zero
    simp only [zero, div_zero, Complex.zero_im, lt_self_iff_false] at upper
  have negativeNonzero : negativeHalfDiagonal prepared.reference time receiver ≠ 0 := by
    intro zero
    simp only [zero, zero_div, Complex.zero_im, lt_self_iff_false] at upper
  have chartSmall : |(pointShapeChart (positiveHalfDiagonal prepared.reference time receiver)
      (negativeHalfDiagonal prepared.reference time receiver)).1| +
      |(pointShapeChart (positiveHalfDiagonal prepared.reference time receiver)
        (negativeHalfDiagonal prepared.reference time receiver)).2| ≤ radius := by
    rw [pointShapeChart_eq_paper_shape_of_upper prepared.reference time receiver upper]
    exact shapeSmall.trans (min_le_left _ _)
  have bound := actual count phase dipoleAngle prepared path time inside receiver
  dsimp only at bound
  rw [← prepared.referenceIdentity] at bound
  exact bound positiveNonzero negativeNonzero chartSmall

end EulerNonuniqueness.Paper
