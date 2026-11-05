import EulerNonuniqueness.Section5.CascadeIndividualSourceStrainContinuity
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect
import EulerNonuniqueness.Section6.PaperRelativeLeadingStrainSum
import EulerNonuniqueness.Section6.PointShapeForcingContinuity
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.eventually_cascade_individual_source_input_continuous (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver ≠ source →
      ContinuousOn (relativeBlockSourceShapeInput {scales with frequency := frequency}
        prepared.trajectory.movingFamily.patchMotion prepared.reference receiver source) (Icc 0 path.stop) := by
  filter_upwards [scales.eventually_cascade_individual_source_strain_continuous amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative
      (by norm_num : (0 : ℝ) < 1 / 4)] with frequency strains referenceSmall
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source different
  let changed : Scales := {scales with frequency := frequency}
  have positions (patch : Fin 4) : Continuous (fun time => patchCentroid prepared.reference time receiver patch) := by
    rw [prepared.referenceIdentity]
    exact prepared.referenceWitness.trajectory.movingFamily.patchCentroid_continuous receiver patch
  have positiveContinuous : Continuous (fun time => positiveHalfDiagonal prepared.reference time receiver) :=
    ((positions 0).sub (positions 1)).div_const 2
  have negativeContinuous : Continuous (fun time => negativeHalfDiagonal prepared.reference time receiver) :=
    ((positions 2).sub (positions 3)).div_const 2
  have small (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      |unstableShape prepared.reference time receiver| + |stableShape prepared.reference time receiver| ≤ 1 / 4 := by
    have actual := referenceSmall prepared time ⟨inside.1, inside.2.trans path.stopBound⟩ receiver
    linarith [abs_nonneg (diagonalDifference prepared.reference time receiver /
      changed.length (receiver.val + 1) ^ 2 - 1)]
  have positiveNonzero (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      positiveHalfDiagonal prepared.reference time receiver ≠ 0 := by
    have upper := paper_shape_ratio_im_pos_of_small prepared.reference time receiver (small time inside)
    intro zero
    simp only [zero, div_zero, Complex.zero_im, lt_self_iff_false] at upper
  have negativeNonzero (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      negativeHalfDiagonal prepared.reference time receiver ≠ 0 := by
    have upper := paper_shape_ratio_im_pos_of_small prepared.reference time receiver (small time inside)
    intro zero
    simp only [zero, zero_div, Complex.zero_im, lt_self_iff_false] at upper
  have actual := strains count phase dipoleAngle prepared path receiver source different
  have difference := actual.1.sub actual.2
  have positiveForcing := difference.mul (continuous_star.comp positiveContinuous).continuousOn
  have negativeForcing := difference.mul (continuous_star.comp negativeContinuous).continuousOn
  have regular := pointShapeForcing_continuousOn positiveContinuous.continuousOn negativeContinuous.continuousOn
    positiveForcing negativeForcing positiveNonzero negativeNonzero
  simpa only [relativeBlockSourceShapeInput, pointShapeForcingCLM_apply, complexStrainPair] using regular

end EulerNonuniqueness.Paper
