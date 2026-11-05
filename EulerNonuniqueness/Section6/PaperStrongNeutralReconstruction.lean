import EulerNonuniqueness.Section6.PaperCorrectedPhaseShapeReconstruction
import EulerNonuniqueness.Section5.CascadeRelativeFirstMomentHistory

noncomputable section

namespace EulerNonuniqueness.Paper

theorem sameGraph_exists_uniform_strong_neutral_reconstruction
    {graph coordinate correction : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (correctionSmooth : ContDiffAt ℝ 1 correction 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
      ∀ {count : ℕ} (scales : Scales) (first second : PatchMotion count) (index : Fin count)
        (time : ℝ) (firstPhase secondPhase : ℝ → ℝ),
      0 < diagonalDifference first time index → 0 < diagonalDifference second time index →
      positiveHalfDiagonal first time index = (‖positiveHalfDiagonal first time index‖ : ℂ) *
        Complex.exp (Complex.I * (firstPhase time : ℂ)) →
      positiveHalfDiagonal second time index = (‖positiveHalfDiagonal second time index‖ : ℂ) *
        Complex.exp (Complex.I * (secondPhase time : ℂ)) →
      |diagonalDifference first time index / scales.length (index.val + 1) ^ 2 - 1| +
        |unstableShape first time index| + |stableShape first time index| < radius →
      |diagonalDifference second time index / scales.length (index.val + 1) ^ 2 - 1| +
        |unstableShape second time index| + |stableShape second time index| < radius →
      ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
          scales.length (index.val + 1) ≤
      (scales.length (index.val + 1) / (4 * scales.location (index.val + 1))) *
        ‖relativeNormalizedFirstMoment scales first second index time‖ +
      constant * (|diagonalDifference first time index - diagonalDifference second time index| /
          scales.length (index.val + 1) ^ 2 +
        |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
        |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2| +
        |correctedPaperPhase correction firstPhase first index time - correctedPaperPhase correction secondPhase second index time|) := by
  obtain ⟨radius, radiusPositive, constant, constantOne, estimate⟩ :=
    sameGraph_exists_uniform_comoving_centroid_reconstruction graphSmooth coordinateSmooth correctionSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  refine ⟨radius, radiusPositive, constant, constantOne, ?_⟩
  intro count scales first second index time firstPhase secondPhase firstPositive secondPositive firstPolar secondPolar firstSmall secondSmall
  let length := scales.length (index.val + 1)
  let location := scales.location (index.val + 1)
  have lengthPositive : 0 < length := scales.length_pos _
  have locationPositive : 0 < location := scales.location_pos _
  have momentIdentity : ‖centroidAsymmetry first time index - centroidAsymmetry second time index‖ / length =
      (length / (4 * location)) * ‖relativeNormalizedFirstMoment scales first second index time‖ := by
    rw [relativeNormalizedFirstMoment, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    change ‖centroidAsymmetry first time index - centroidAsymmetry second time index‖ / length =
      (length / (4 * location)) * ((4 * location / length ^ 2) *
        ‖centroidAsymmetry first time index - centroidAsymmetry second time index‖)
    field_simp [lengthPositive.ne', locationPositive.ne']
    <;> ring
  have dilationIdentity : |diagonalDifference first time index / length ^ 2 - diagonalDifference second time index / length ^ 2| =
      |diagonalDifference first time index - diagonalDifference second time index| / length ^ 2 := by
    rw [← sub_div, abs_div, abs_of_pos (sq_pos_of_pos lengthPositive)]
  let bound := (length / (4 * location)) * ‖relativeNormalizedFirstMoment scales first second index time‖ +
    constant * (|diagonalDifference first time index - diagonalDifference second time index| / length ^ 2 +
      |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
      |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2| +
      |correctedPaperPhase correction firstPhase first index time - correctedPaperPhase correction secondPhase second index time|)
  have boundNonnegative : 0 ≤ bound := by dsimp only [bound]; positivity
  have pointwise (patch : Fin 4) :
      ‖(patchCentroid first time index patch - quadrupoleCenter first time index) -
        (patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length ≤ bound := by
    have actual := estimate first second index time length (firstPhase time) (secondPhase time) lengthPositive
      firstPositive secondPositive firstPolar secondPolar firstSmall secondSmall patch
    rw [momentIdentity, dilationIdentity] at actual
    exact actual
  have normBound : ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
      (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ ≤ bound * length := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg boundNonnegative lengthPositive.le)).mpr
    intro patch
    exact (div_le_iff₀ lengthPositive).mp (pointwise patch)
  exact (div_le_iff₀ lengthPositive).mpr normBound

end EulerNonuniqueness.Paper
