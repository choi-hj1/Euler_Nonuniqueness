import EulerNonuniqueness.Section6.CorrectedPhaseShapeRelative

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem sameGraph_exists_uniform_comoving_centroid_reconstruction
    {graph coordinate correction : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (correctionSmooth : ContDiffAt ℝ 1 correction 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
    ∀ {count : ℕ} (first second : PatchMotion count) (index : Fin count) (time length firstPhase secondPhase : ℝ),
    0 < length →
    0 < diagonalDifference first time index → 0 < diagonalDifference second time index →
    positiveHalfDiagonal first time index = (‖positiveHalfDiagonal first time index‖ : ℂ) * Complex.exp (Complex.I * (firstPhase : ℂ)) →
    positiveHalfDiagonal second time index = (‖positiveHalfDiagonal second time index‖ : ℂ) * Complex.exp (Complex.I * (secondPhase : ℂ)) →
    |diagonalDifference first time index / length ^ 2 - 1| +
      |unstableShape first time index| + |stableShape first time index| < radius →
    |diagonalDifference second time index / length ^ 2 - 1| +
      |unstableShape second time index| + |stableShape second time index| < radius →
    ∀ patch : Fin 4,
    ‖(patchCentroid first time index patch - quadrupoleCenter first time index) -
      (patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length ≤
    ‖centroidAsymmetry first time index - centroidAsymmetry second time index‖ / length +
      constant * (|diagonalDifference first time index / length ^ 2 - diagonalDifference second time index / length ^ 2| +
        |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
        |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2| +
        |correctedPaperPhase correction (fun _ => firstPhase) first index time -
          correctedPaperPhase correction (fun _ => secondPhase) second index time|) := by
  obtain ⟨radius, radiusPositive, constant, constantOne, bound⟩ :=
    sameGraph_correctedHalfDiagonalProfile_exists_relative_chart_bound graphSmooth coordinateSmooth correctionSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  refine ⟨radius, radiusPositive, constant, constantOne, ?_⟩
  intro count first second index time length firstPhase secondPhase lengthPositive firstPositive secondPositive
    firstPolar secondPolar firstSmall secondSmall patch
  let firstRaw := (unstableShape first time index, stableShape first time index)
  let secondRaw := (unstableShape second time index, stableShape second time index)
  let firstData := (diagonalDifference first time index / length ^ 2, firstRaw)
  let secondData := (diagonalDifference second time index / length ^ 2, secondRaw)
  let firstAdjusted := correctedPaperPhase correction (fun _ => firstPhase) first index time
  let secondAdjusted := correctedPaperPhase correction (fun _ => secondPhase) second index time
  let firstCentral := centrallySymmetricFourPoint (positiveHalfDiagonal first time index) (negativeHalfDiagonal first time index)
  let secondCentral := centrallySymmetricFourPoint (positiveHalfDiagonal second time index) (negativeHalfDiagonal second time index)
  have firstReconstruction : firstCentral = (length : ℂ) •
      (Complex.exp (Complex.I * (firstAdjusted : ℂ)) • correctedHalfDiagonalProfile correction firstData) :=
    correctedHalfDiagonalProfile_polar_reconstruction correction _ _ lengthPositive firstPositive firstPolar
  have secondReconstruction : secondCentral = (length : ℂ) •
      (Complex.exp (Complex.I * (secondAdjusted : ℂ)) • correctedHalfDiagonalProfile correction secondData) :=
    correctedHalfDiagonalProfile_polar_reconstruction correction _ _ lengthPositive secondPositive secondPolar
  have centralBound := bound firstData secondData firstSmall secondSmall firstAdjusted secondAdjusted
  have centralNorm : ‖firstCentral - secondCentral‖ / length =
      ‖Complex.exp (Complex.I * (firstAdjusted : ℂ)) • correctedHalfDiagonalProfile correction firstData -
        Complex.exp (Complex.I * (secondAdjusted : ℂ)) • correctedHalfDiagonalProfile correction secondData‖ := by
    rw [firstReconstruction, secondReconstruction, ← smul_sub, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos lengthPositive]
    field_simp
  have offsetBound (positiveFirst negativeFirst asymmetryFirst positiveSecond negativeSecond asymmetrySecond : ℂ)
      (patch : Fin 4) :
      ‖quadrupoleCentroidOffset positiveFirst negativeFirst asymmetryFirst patch -
        quadrupoleCentroidOffset positiveSecond negativeSecond asymmetrySecond patch‖ ≤
      ‖asymmetryFirst - asymmetrySecond‖ +
        ‖centrallySymmetricFourPoint positiveFirst negativeFirst - centrallySymmetricFourPoint positiveSecond negativeSecond‖ := by
    have identity : quadrupoleCentroidOffset positiveFirst negativeFirst asymmetryFirst patch -
        quadrupoleCentroidOffset positiveSecond negativeSecond asymmetrySecond patch =
        patchSign patch • (asymmetryFirst - asymmetrySecond) +
          (centrallySymmetricFourPoint positiveFirst negativeFirst - centrallySymmetricFourPoint positiveSecond negativeSecond) patch := by
      fin_cases patch <;> norm_num [quadrupoleCentroidOffset, centrallySymmetricFourPoint, patchSign, Fin.ext_iff] <;> ring
    rw [identity]
    apply (norm_add_le _ _).trans
    have sign : |patchSign patch| = 1 := by fin_cases patch <;> norm_num [patchSign]
    rw [norm_smul, Real.norm_eq_abs, sign, one_mul]
    exact add_le_add_left (norm_le_pi_norm _ patch) _
  rw [quadrupole_centroid_offset_reconstruction first time index patch,
    quadrupole_centroid_offset_reconstruction second time index patch]
  have estimate := div_le_div_of_nonneg_right
    (offsetBound (positiveHalfDiagonal first time index) (negativeHalfDiagonal first time index)
      (centroidAsymmetry first time index) (positiveHalfDiagonal second time index)
      (negativeHalfDiagonal second time index) (centroidAsymmetry second time index) patch) lengthPositive.le
  rw [add_div] at estimate
  apply estimate.trans
  apply add_le_add_left
  rw [centralNorm]
  exact centralBound

end EulerNonuniqueness.Paper
