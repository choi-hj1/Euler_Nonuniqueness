import EulerNonuniqueness.Section6.ForcedAdjustedPhaseEquation
import EulerNonuniqueness.Section6.PaperSmallShapeDiagonalDynamics

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6 EulerNonuniqueness.Section2

def correctedPaperPhase {count : ℕ} (correction phase : ℝ → ℝ) (motion : PatchMotion count)
    (index : Fin count) (time : ℝ) : ℝ :=
  phase time - (Real.sqrt 2 - 1) / 4 *
    shapeChartAngle (unstableShape motion time index, stableShape motion time index) -
    correction (unstableShape motion time index)

def correctedPaperPhaseForcing {count : ℕ} (scales : Scales) (correction : ℝ → ℝ)
    (motion : PatchMotion count) (index : Fin count) (time : ℝ) : ℝ :=
  let forcing := fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
    (fun patch => patchCentroid motion time index patch) (quadrupoleCentroidForcing scales motion time index)
  (forcing.1 / positiveHalfDiagonal motion time index).im -
    (Real.sqrt 2 - 1) / 4 * Real.sqrt 2 *
      ((referencePointShapeForcing scales motion time index).1 - (referencePointShapeForcing scales motion time index).2) -
    deriv correction (unstableShape motion time index) * (referencePointShapeForcing scales motion time index).1

theorem paper_small_shape_central_point_geometry {count : ℕ} (motion : PatchMotion count) (time : ℝ) (index : Fin count)
    (small : |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4) :
    FourPointNoncollision (centrallySymmetricFourPoint (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)) ∧
      ‖negativeHalfDiagonal motion time index‖ < ‖positiveHalfDiagonal motion time index‖ := by
  have upper := paper_shape_ratio_im_pos_of_small motion time index small
  have identity := pointShapeChart_eq_paper_shape_of_upper motion time index upper
  have chartSmall : |(pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).1| +
      |(pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).2| ≤ 1 / 4 := by
    simpa only [identity] using small
  obtain ⟨positiveNonzero, negativeNonzero, _, ratioUpper⟩ :=
    pointShapeChart_reference_annulus (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) chartSmall
  have positiveNorm : 0 < ‖positiveHalfDiagonal motion time index‖ := norm_pos_iff.mpr positiveNonzero
  have normOrder : ‖negativeHalfDiagonal motion time index‖ < ‖positiveHalfDiagonal motion time index‖ := by
    have scaled := (div_le_iff₀ positiveNorm).mp ratioUpper
    linarith
  have differenceNonzero : positiveHalfDiagonal motion time index - negativeHalfDiagonal motion time index ≠ 0 := by
    intro zero
    rw [sub_eq_zero.mp zero] at normOrder
    exact lt_irrefl _ normOrder
  have sumNonzero : positiveHalfDiagonal motion time index + negativeHalfDiagonal motion time index ≠ 0 := by
    intro zero
    have equality : negativeHalfDiagonal motion time index = -positiveHalfDiagonal motion time index :=
      eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using zero)
    rw [equality, norm_neg] at normOrder
    exact lt_irrefl _ normOrder
  exact ⟨centrallySymmetricFourPoint_noncollision positiveNonzero negativeNonzero differenceNonzero sumNonzero, normOrder⟩

theorem FinitePatchEvolution.correctedPaperPhase_hasDerivAt
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonPositive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (radii : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (separated : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    (index : Fin count) (inside : time ∈ Ioo 0 horizon)
    (small : |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4)
    {correction phase : ℝ → ℝ}
    (phaseEquation : HasDerivAt phase
      (deriv (fun current => positiveHalfDiagonal motion current index) time / positiveHalfDiagonal motion time index).im time)
    (correctionDifferentiable : DifferentiableAt ℝ correction (unstableShape motion time index)) :
    let frequency := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 / diagonalDifference motion time index
    HasDerivAt (correctedPaperPhase correction phase motion index)
      (-frequency + frequency * correctedPhaseError 1 correction (unstableShape motion time index, stableShape motion time index) +
        correctedPaperPhaseForcing scales correction motion index time) time := by
  let raw := fun current => (unstableShape motion current index, stableShape motion current index)
  let frequency := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 / diagonalDifference motion time index
  let forcing := referencePointShapeForcing scales motion time index
  have equation := evolution.centroid_paper_shape_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive
    frequencyPositive ratioPositive radii control separated index inside small
  change HasDerivAt raw (shapeChartVelocity frequency (raw time) + forcing) time at equation
  have geometry := paper_small_shape_central_point_geometry motion time index small
  have phaseRate := evolution.centroid_positive_phase_rate_of_boundary_gaps horizonPositive amplitudePositive
    frequencyPositive ratioPositive radii control separated index inside geometry.1 geometry.2
  have upper := paper_shape_ratio_im_pos_of_small motion time index small
  have coherent := pointShapeChart_eq_paper_shape_of_upper motion time index upper
  have ratioIdentity := (shapeChart_reconstruction
    (pointShapeRatio (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index))
    (pointShapeAngle (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index))).1
  have angleIdentity := (shapeChart_reconstruction
    (pointShapeRatio (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index))
    (pointShapeAngle (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index))).2
  change shapeChartRatio (pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)) = _ at ratioIdentity
  change shapeChartAngle (pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)) = _ at angleIdentity
  rw [coherent] at ratioIdentity angleIdentity
  dsimp only at phaseRate
  rw [← ratioIdentity, ← angleIdentity] at phaseRate
  have actualPhase := phaseEquation
  rw [phaseRate] at actualPhase
  have adjusted := adjustedPhase_forced_hasDerivAt equation actualPhase
  let phaseForcing := ((fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
      (fun patch => patchCentroid motion time index patch) (quadrupoleCentroidForcing scales motion time index)).1 /
        positiveHalfDiagonal motion time index).im -
      (Real.sqrt 2 - 1) / 4 * Real.sqrt 2 * (forcing.1 - forcing.2)
  have adjustedEquation : HasDerivAt
      (fun current => phase current - (Real.sqrt 2 - 1) / 4 * shapeChartAngle (raw current))
      (-frequency + adjustedPhaseError frequency (raw time) + phaseForcing) time := by
    convert adjusted using 1
    dsimp only [phaseForcing]
    ring
  have corrected := correctedPhase_forced_equation equation adjustedEquation correctionDifferentiable
  rw [correctedPhaseError_frequency_mul] at corrected
  convert corrected using 1
  dsimp only [correctedPaperPhaseForcing, phaseForcing, raw, forcing]
  ring

end EulerNonuniqueness.Paper
