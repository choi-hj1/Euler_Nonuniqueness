import EulerNonuniqueness.Section6.SourcePacketUniformReceiverFieldGeometry
import EulerNonuniqueness.Section4.PaperPhaseDilationEstimates

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem exists_source_packet_material_phase_rate :
    ∃ internal ≥ (0 : ℝ), ∃ momentRadius > (0 : ℝ), ∃ phaseConstant ≥ (0 : ℝ), ∃ phaseRadius > (0 : ℝ),
    ∀ {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
      {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
        scaleRoot shapeRadius factor monitor boundaryConstant count},
    ∀ path : CascadeInternallyStoppedPath prepared,
    0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ time ∈ Icc 0 path.stop, ∀ index : Fin count,
    ReferenceCentroidFieldGeometry scales prepared.trajectory.movingFamily.patchMotion time index →
    ∀ deformation memory bound : ℝ,
    (∀ patch, BoundaryCloseToCircle scales prepared.trajectory.movingFamily.patchMotion time index patch deformation) →
    0 ≤ deformation → deformation ≤ 1 / 16 → 0 ≤ memory → 0 ≤ bound →
    deformation ≤ bound / scales.omega (index.val + 1) ^ 2 →
    scales.length (index.val + 1) ≤ 1 → scales.hessian ≤ 1 →
    scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference prepared.trajectory.movingFamily.patchMotion time index →
    ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤ memory * scales.length (index.val + 1) ^ 2 →
    scales.length (index.val + 1) < momentRadius / (8 * (memory + 1)) →
    |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 4 →
    |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| < phaseRadius →
    |referencePhaseError scales prepared.trajectory.movingFamily.patchMotion index time| ≤
      2 * phaseConstant * scales.omega (index.val + 1) *
        (|unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
          |stableShape prepared.trajectory.movingFamily.patchMotion time index|) +
        referenceOddForcingBudget scales (index.val + 1) internal memory bound := by
  obtain ⟨internal, internalNonnegative, momentRadius, momentRadiusPositive, forcingEstimate⟩ :=
    exists_uniform_reference_odd_forcing_bound
  obtain ⟨phaseConstant, phaseConstantNonnegative, phaseRadius, phaseRadiusPositive, phaseEstimate⟩ :=
    exists_uniform_forced_point_phase_error_bound
  refine ⟨internal, internalNonnegative, momentRadius, momentRadiusPositive, phaseConstant, phaseConstantNonnegative,
    phaseRadius, phaseRadiusPositive, ?_⟩
  intro scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor
    boundaryConstant count prepared path amplitudePositive frequencyOne ratioBound alphaPositive time inside index geometry
    deformation memory bound control deformationNonnegative deformationSmall memoryNonnegative boundNonnegative
    deformationBound lengthOne hessianOne differenceLower asymmetryBound lengthSmall chartSmall chartPhaseSmall
  let family := prepared.trajectory.movingFamily
  let motion := family.patchMotion
  let positive := positiveHalfDiagonal motion time index
  let negative := negativeHalfDiagonal motion time index
  let positions := fun patch => patchCentroid motion time index patch
  let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
  let forcing := fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales motion time index)
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < scales.ratio := by linarith
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := scales.length_pos (index.val + 1)
  have chartIdentity : pointShapeChart positive negative = (unstableShape motion time index, stableShape motion time index) :=
    pointShapeChart_eq_paper_shape_of_upper motion time index (paper_shape_ratio_im_pos_of_small motion time index chartSmall)
  have coherentSmall : |(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2| ≤ 1 / 4 := by
    simpa only [chartIdentity] using chartSmall
  obtain ⟨positiveNonzero, negativeNonzero, _, ratioUpper⟩ := pointShapeChart_reference_annulus positive negative coherentSmall
  have positiveNorm : 0 < ‖positive‖ := norm_pos_iff.mpr positiveNonzero
  have negativeSmall : ‖negative‖ ≤ ‖positive‖ / 2 := by
    have scaled := (div_le_iff₀ positiveNorm).mp ratioUpper
    linarith
  have normOrder : ‖negative‖ < ‖positive‖ := by linarith
  have differenceNonzero : positive - negative ≠ 0 := by
    intro zero
    rw [sub_eq_zero.mp zero] at normOrder
    exact lt_irrefl _ normOrder
  have sumNonzero : positive + negative ≠ 0 := by
    intro zero
    have equality : negative = -positive := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using zero)
    rw [equality, norm_neg] at normOrder
    exact lt_irrefl _ normOrder
  have squareNonzero : star positive ^ 2 - star negative ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (by simpa only [star_add] using star_ne_zero.mpr sumNonzero)
      (by simpa only [star_sub] using star_ne_zero.mpr differenceNonzero)
  have momentSmall := reference_normalized_signed_moment_small scales motion time index memoryNonnegative
    momentRadiusPositive differenceLower asymmetryBound lengthSmall
  have forcingBound : ‖forcing‖ / ‖positive‖ ≤ referenceOddForcingBudget scales (index.val + 1) internal memory bound :=
    forcingEstimate path.evolution inside amplitudePositive frequencyOne ratioBound alphaPositive index geometry control
      deformationNonnegative deformationSmall memoryNonnegative boundNonnegative deformationBound lengthOne hessianOne
      differenceLower asymmetryBound momentSmall coherentSmall
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have material (patch : Fin 4) (label : ℝ) := path.material_boundary inside (finProdFinEquiv (index, patch)) label
  have actual := fourPointOddPart_actual_forced_equation (trajectory := fun current patch => patchCentroid motion current index patch)
    (forcing := quadrupoleCentroidForcing scales motion time index)
    (fun patch => by simpa only [quadrupoleCentroidForcing, add_assoc] using
      family.patchCentroid_hasDerivAt_point_field path.evolution inside index patch globalInside (material patch))
  have positiveDerivative := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt time actual
  have derivativeIdentity : deriv (fun current => positiveHalfDiagonal motion current index) time =
      positivePointVelocity coefficient positive negative + forcing.1 := by
    exact positiveDerivative.deriv
  have differencePositive : 0 < diagonalDifference motion time index :=
    (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le differenceLower
  have rateIdentity : scales.omega (index.val + 1) / referenceDilation scales motion index time =
      coefficient / diagonalDifference motion time index := by
    unfold referenceDilation coefficient
    field_simp <;> ring
  have rateBound : coefficient / diagonalDifference motion time index ≤ 2 * scales.omega (index.val + 1) := by
    apply (div_le_iff₀ differencePositive).mpr
    dsimp only [coefficient]
    nlinarith only [mul_le_mul_of_nonneg_left differenceLower omegaPositive.le]
  have pointSmall : ‖pointShapeChart positive negative‖ < phaseRadius := by
    rw [chartIdentity, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _)).trans_lt chartPhaseSmall
  have estimate := phaseEstimate coefficient positive negative forcing (by dsimp only [coefficient]; positivity)
    positiveNonzero negativeNonzero squareNonzero normOrder pointSmall
  have phaseIdentity : referencePhaseError scales motion index time =
      ((positivePointVelocity coefficient positive negative + forcing.1) / positive).im +
        coefficient / diagonalDifference motion time index := by
    unfold referencePhaseError
    rw [derivativeIdentity, rateIdentity]
  rw [phaseIdentity]
  apply estimate.trans
  apply add_le_add _ forcingBound
  have chartBound : ‖pointShapeChart positive negative‖ ≤ |unstableShape motion time index| + |stableShape motion time index| := by
    rw [chartIdentity, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _)
  calc
    _ ≤ phaseConstant * (2 * scales.omega (index.val + 1)) *
        (|unstableShape motion time index| + |stableShape motion time index|) := by
      gcongr
      exact rateBound
    _ = _ := by ring

end EulerNonuniqueness.Paper
