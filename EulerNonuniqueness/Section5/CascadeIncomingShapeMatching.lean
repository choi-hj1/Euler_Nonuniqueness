import EulerNonuniqueness.Section6.HalfDiagonalConfigurationMatching
import EulerNonuniqueness.Section5.CascadeNormalizedPointEquation

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_cascade_incoming_shape_matching
    (referencePositive referenceNegative : ℂ)
    (referenceDifference : 0 < ‖referencePositive‖ ^ 2 - ‖referenceNegative‖ ^ 2)
    {accuracy : ℝ} (accuracyPositive : 0 < accuracy) :
    ∃ tolerance > (0 : ℝ), ∀ {count : ℕ} (scales : Scales) (motion : PatchMotion count)
      (time : ℝ) (index : Fin count),
      0 < diagonalDifference motion time index →
      |diagonalDifference motion time index / scales.length (index.val + 1) ^ 2 -
        (‖referencePositive‖ ^ 2 - ‖referenceNegative‖ ^ 2)| < tolerance →
      |unstableShape motion time index - (halfDiagonalShape referencePositive referenceNegative).1| +
        |stableShape motion time index - (halfDiagonalShape referencePositive referenceNegative).2| < tolerance →
      ‖centroidAsymmetry motion time index‖ / scales.length (index.val + 1) < tolerance →
      ∃ rotation : ℂ, ‖rotation‖ = 1 ∧
        ‖cascadeNormalizedPointPositions scales motion index time rotation 0 -
          centrallySymmetricFourPoint referencePositive referenceNegative‖ < accuracy := by
  obtain ⟨tolerance, tolerancePositive, matching⟩ :=
    exists_halfDiagonal_configuration_matching referencePositive referenceNegative referenceDifference accuracyPositive
  refine ⟨tolerance, tolerancePositive, ?_⟩
  intro count scales motion time index differencePositive differenceClose shapeClose asymmetryClose
  have shapeIdentity : halfDiagonalShape (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) =
      (unstableShape motion time index, stableShape motion time index) := rfl
  have shapeBound : ‖halfDiagonalShape (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) -
      halfDiagonalShape referencePositive referenceNegative‖ < tolerance := by
    rw [shapeIdentity, Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, max_lt_iff]
    constructor <;> linarith [abs_nonneg (unstableShape motion time index - (halfDiagonalShape referencePositive referenceNegative).1),
      abs_nonneg (stableShape motion time index - (halfDiagonalShape referencePositive referenceNegative).2)]
  obtain ⟨rotation, rotationNorm, close⟩ := matching (positiveHalfDiagonal motion time index)
    (negativeHalfDiagonal motion time index) (centroidAsymmetry motion time index) (scales.length (index.val + 1))
    (scales.length_pos _) differencePositive differenceClose shapeBound asymmetryClose
  refine ⟨rotation, rotationNorm, ?_⟩
  have identity : cascadeNormalizedPointPositions scales motion index time rotation 0 =
      fun patch => ((scales.length (index.val + 1) : ℂ) * rotation)⁻¹ *
        quadrupoleCentroidOffset (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)
          (centroidAsymmetry motion time index) patch := by
    funext patch
    simp only [cascadeNormalizedPointPositions, zero_div, add_zero, fourPointCenterProjection]
    change _ * (patchCentroid motion time index patch - quadrupoleCenter motion time index) = _
    rw [patchCentroid_sub_quadrupoleCenter]
    rfl
  rw [identity]
  exact close

end EulerNonuniqueness.Paper
