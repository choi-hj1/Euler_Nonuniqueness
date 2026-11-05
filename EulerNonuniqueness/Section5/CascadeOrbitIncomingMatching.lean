import EulerNonuniqueness.Section5.CascadeIncomingShapeMatching

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem normalizedSeparatingOrbit_exists_incoming_shape_matching
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit) (incomingTime : ℝ)
    {accuracy : ℝ} (accuracyPositive : 0 < accuracy) :
    ∃ tolerance > (0 : ℝ), ∀ {count : ℕ} (scales : Scales) (motion : PatchMotion count)
      (time : ℝ) (index : Fin count),
      0 < diagonalDifference motion time index →
      |diagonalDifference motion time index / scales.length (index.val + 1) ^ 2 - 1| < tolerance →
      |unstableShape motion time index - orbitUnstableShape orbit incomingTime| +
        |stableShape motion time index - orbitStableShape orbit incomingTime| < tolerance →
      ‖centroidAsymmetry motion time index‖ / scales.length (index.val + 1) < tolerance →
      ∃ rotation : ℂ, ‖rotation‖ = 1 ∧
        ‖cascadeNormalizedPointPositions scales motion index time rotation 0 -
          centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ < accuracy := by
  have difference := (normalized.2.1 incomingTime).1
  obtain ⟨tolerance, tolerancePositive, matching⟩ := exists_cascade_incoming_shape_matching
    (orbit.positive incomingTime) (orbit.negative incomingTime) (by rw [difference]; norm_num) accuracyPositive
  refine ⟨tolerance, tolerancePositive, ?_⟩
  intro count scales motion time index differencePositive differenceClose shapeClose asymmetryClose
  apply matching scales motion time index differencePositive
  · simpa only [difference] using differenceClose
  · exact shapeClose
  · exact asymmetryClose

end EulerNonuniqueness.Paper
