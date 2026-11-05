import EulerNonuniqueness.Section4.PaperHalfDiagonalDynamics
import EulerNonuniqueness.Section4.PaperCoarseUpperBranch
import EulerNonuniqueness.Section4.ReferencePhaseDilationEstimates

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem exists_uniform_paper_phase_dilation_estimates :
    ∃ internal ≥ (0 : ℝ), ∃ momentRadius > (0 : ℝ), ∃ phaseConstant ≥ (0 : ℝ), ∃ phaseRadius > (0 : ℝ),
      ∀ {count : ℕ} {scales : Scales} {motion : PatchMotion count}
        {horizon time deformation memory bound : ℝ},
      ∀ (evolution : FinitePatchEvolution scales motion horizon), 0 < horizon →
      0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      (∀ index : Fin count, 0 < scales.radius (index.val + 1)) →
      (∀ current ∈ Icc 0 horizon, ∀ index patch,
        ∃ error ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch error) →
      (∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
        (other, otherPatch) ≠ (index, patch) →
        8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
          dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0)) →
      time ∈ Ioo 0 horizon → ∀ index : Fin count,
      ReferenceCentroidFieldGeometry scales motion time index →
      (∀ patch, BoundaryCloseToCircle scales motion time index patch deformation) →
      0 ≤ deformation → deformation ≤ 1 / 16 → 0 ≤ memory → 0 ≤ bound →
      deformation ≤ bound / scales.omega (index.val + 1) ^ 2 → scales.length (index.val + 1) ≤ 1 → scales.hessian ≤ 1 →
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index →
      diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2 →
      ‖centroidAsymmetry motion time index‖ ≤ memory * scales.length (index.val + 1) ^ 2 →
      scales.length (index.val + 1) < momentRadius / (8 * (memory + 1)) →
      |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4 →
      |deriv (referenceDilation scales motion index) time| ≤
          12 * referenceOddForcingBudget scales (index.val + 1) internal memory bound ∧
        (|unstableShape motion time index| + |stableShape motion time index| < phaseRadius →
          |referencePhaseError scales motion index time| ≤
            2 * phaseConstant * scales.omega (index.val + 1) *
              (|unstableShape motion time index| + |stableShape motion time index|) +
            referenceOddForcingBudget scales (index.val + 1) internal memory bound) := by
  obtain ⟨internal, internalNonnegative, momentRadius, momentRadiusPositive, forcingEstimate⟩ :=
    exists_uniform_reference_odd_forcing_bound
  obtain ⟨phaseConstant, phaseConstantNonnegative, phaseRadius, phaseRadiusPositive, phaseEstimate⟩ :=
    exists_uniform_forced_point_phase_error_bound
  refine ⟨internal, internalNonnegative, momentRadius, momentRadiusPositive, phaseConstant, phaseConstantNonnegative,
    phaseRadius, phaseRadiusPositive, ?_⟩
  intro count scales motion horizon time deformation memory bound evolution horizonPositive amplitudePositive
    frequencyBound ratioBound alphaPositive radiusPositive passiveControl labelGaps inside index geometry control
    nonnegative small memoryNonnegative boundNonnegative deformationBound lengthBound hessianBound differenceLower
    differenceUpper asymmetryBound lengthSmall chartSmall
  let positive := positiveHalfDiagonal motion time index
  let negative := negativeHalfDiagonal motion time index
  let positions := fun patch => patchCentroid motion time index patch
  let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
  let forcing := fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales motion time index)
  let budget := referenceOddForcingBudget scales (index.val + 1) internal memory bound
  have upper := paper_shape_ratio_im_pos_of_small motion time index chartSmall
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := scales.length_pos (index.val + 1)
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have budgetNonnegative : 0 ≤ budget := by dsimp only [budget, referenceOddForcingBudget]; positivity
  have chartIdentity : pointShapeChart positive negative = (unstableShape motion time index, stableShape motion time index) :=
    pointShapeChart_eq_paper_shape_of_upper motion time index upper
  have coherentSmall : |(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2| ≤ 1 / 4 := by
    simpa only [chartIdentity] using chartSmall
  obtain ⟨positiveNonzero, negativeNonzero, _, ratioUpper⟩ := pointShapeChart_reference_annulus positive negative coherentSmall
  have positiveNorm : 0 < ‖positive‖ := norm_pos_iff.mpr positiveNonzero
  have negativeSmall : ‖negative‖ ≤ ‖positive‖ / 2 := by
    have scaled := (div_le_iff₀ positiveNorm).mp ratioUpper
    linarith only [scaled]
  have normOrder : ‖negative‖ < ‖positive‖ := by linarith only [negativeSmall, positiveNorm]
  have differenceNonzero : positive - negative ≠ 0 := by
    intro zero
    rw [sub_eq_zero.mp zero] at normOrder
    exact lt_irrefl _ normOrder
  have sumNonzero : positive + negative ≠ 0 := by
    intro zero
    have equality : negative = -positive := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using zero)
    rw [equality, norm_neg] at normOrder
    exact lt_irrefl _ normOrder
  have noncollision := centrallySymmetricFourPoint_noncollision positiveNonzero negativeNonzero differenceNonzero sumNonzero
  have squareNonzero : star positive ^ 2 - star negative ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (by simpa only [star_add] using star_ne_zero.mpr sumNonzero)
      (by simpa only [star_sub] using star_ne_zero.mpr differenceNonzero)
  have momentSmall := reference_normalized_signed_moment_small scales motion time index memoryNonnegative
    momentRadiusPositive differenceLower asymmetryBound lengthSmall
  have forcingBound : ‖forcing‖ / ‖positive‖ ≤ budget :=
    forcingEstimate evolution ⟨inside.1.le, inside.2.le⟩ amplitudePositive frequencyBound ratioBound alphaPositive index geometry
      control nonnegative small memoryNonnegative boundNonnegative deformationBound lengthBound hessianBound
      differenceLower asymmetryBound momentSmall coherentSmall
  have differencePositive : 0 < diagonalDifference motion time index :=
    (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le differenceLower
  have rateIdentity : scales.omega (index.val + 1) / referenceDilation scales motion index time =
      coefficient / diagonalDifference motion time index := by
    unfold referenceDilation coefficient
    field_simp
    <;> ring
  have rateBound : coefficient / diagonalDifference motion time index ≤ 2 * scales.omega (index.val + 1) := by
    apply (div_le_iff₀ differencePositive).mpr
    dsimp only [coefficient]
    nlinarith only [mul_le_mul_of_nonneg_left differenceLower omegaPositive.le]
  constructor
  · have equation := (evolution.centroid_diagonalDifference_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive
      frequencyPositive ratioPositive radiusPositive passiveControl labelGaps index inside noncollision normOrder).div_const
      (scales.length (index.val + 1) ^ 2)
    have derivativeIdentity : deriv (referenceDilation scales motion index) time =
        (2 * @inner ℝ ℂ _ positive forcing.1 - 2 * @inner ℝ ℂ _ negative forcing.2) /
          scales.length (index.val + 1) ^ 2 := equation.deriv
    rw [derivativeIdentity]
    exact point_dilation_forcing_rate_bound lengthPositive positiveNonzero negativeSmall differenceUpper budgetNonnegative forcingBound
  · intro phaseSmall
    have pointSmall : ‖pointShapeChart positive negative‖ < phaseRadius := by
      rw [chartIdentity, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _)).trans_lt phaseSmall
    have actual := phaseEstimate coefficient positive negative forcing coefficientNonnegative positiveNonzero negativeNonzero
      squareNonzero normOrder pointSmall
    have phaseIdentity := evolution.centroid_positive_phase_rate_of_boundary_gaps horizonPositive amplitudePositive
      frequencyPositive ratioPositive radiusPositive passiveControl labelGaps index inside noncollision normOrder
    have targetIdentity : referencePhaseError scales motion index time =
        ((positivePointVelocity coefficient positive negative + forcing.1) / positive).im +
          coefficient / diagonalDifference motion time index := by
      rw [referencePhaseError, rateIdentity, phaseIdentity]
      rw [add_div, Complex.add_im, positive_point_log_im_eq_rotation coefficient positiveNonzero negativeNonzero squareNonzero normOrder]
      rfl
    rw [targetIdentity]
    apply actual.trans
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
