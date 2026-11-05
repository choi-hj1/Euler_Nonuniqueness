import EulerNonuniqueness.Section5.CascadeCoarserLeadingMacroFeedback
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect
import EulerNonuniqueness.Section4.PaperCoarseUpperBranch

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_actual_coarser_leading_actual_feedback :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ time ∈ Icc 0 path.stop, ∀ receiver : Fin count,
    let changed : Scales := {scales with frequency := frequency}
    ‖∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val),
      relativeBlockSourceShapeInput changed prepared.trajectory.movingFamily.patchMotion prepared.reference receiver source time‖ ≤
      (constant / changed.location (receiver.val + 1) ^ 4) *
        (216360000 * changed.hessian + 576 * changed.strain) *
          ‖fun source : Fin count => if source.val ≤ receiver.val then
            changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖ := by
  obtain ⟨rawCap, rawPositive, chartRadius, chartPositive, constant, constantNonnegative, bounds⟩ :=
    exists_uniform_actual_coarser_leading_macro_feedback
  refine ⟨rawCap, rawPositive, constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  have smallPositive : 0 < min chartRadius (1 / 4 : ℝ) := lt_min chartPositive (by norm_num)
  filter_upwards [bounds scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative smallPositive]
    with frequency actual sharp
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver
  dsimp only
  have defect := sharp prepared.toCascadeMaterialPreparedPair time ⟨inside.1, inside.2.trans path.stopBound⟩ receiver
  have shapeSmall : |unstableShape prepared.reference time receiver| + |stableShape prepared.reference time receiver| ≤
      min chartRadius (1 / 4 : ℝ) := by
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
        (negativeHalfDiagonal prepared.reference time receiver)).2| ≤ chartRadius := by
    rw [pointShapeChart_eq_paper_shape_of_upper prepared.reference time receiver upper]
    exact shapeSmall.trans (min_le_left _ _)
  exact actual count phase dipoleAngle prepared path time inside receiver positiveNonzero negativeNonzero chartSmall

end EulerNonuniqueness.Paper
