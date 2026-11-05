import EulerNonuniqueness.Section4.ReferenceOddForcing
import EulerNonuniqueness.Section4.ReferenceHalfDiagonalDynamics
import EulerNonuniqueness.Section4.ReferencePhaseKinematics
import EulerNonuniqueness.Section4.ReferenceNeutralNormalization
import EulerNonuniqueness.Section6.PointPhaseDilationBound

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

def referenceOddForcingBudget (scales : Scales) (index : ℕ) (internal memory bound : ℝ) : ℝ :=
  ((2 * internal * memory ^ 2 + 4608) / Real.pi) * scales.strain +
    ((27648000000 + 226492416 / Real.pi) * bound / scales.amplitude) / scales.omega index ^ 4

set_option maxHeartbeats 2000000

theorem exists_uniform_reference_phase_dilation_estimates :
    ∃ internal ≥ (0 : ℝ), ∃ momentRadius > (0 : ℝ), ∃ phaseConstant ≥ (0 : ℝ), ∃ phaseRadius > (0 : ℝ),
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales}
        {horizon time deformation memory bound : ℝ},
      ∀ (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon),
      0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ (index : Fin count),
      (∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
        (family.patch (finProdFinEquiv (index, patch))).finalTime) →
      (∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
        biotSavart (Paper.patchVorticity scales family.patchMotion time)
          ((family.patch (finProdFinEquiv (index, patch))).boundary time label)) →
      ReferenceCentroidFieldGeometry scales family.patchMotion time index →
      (∀ patch, BoundaryCloseToCircle scales family.patchMotion time index patch deformation) →
      0 ≤ deformation → deformation ≤ 1 / 16 → 0 ≤ memory → 0 ≤ bound →
      deformation ≤ bound / scales.omega (index.val + 1) ^ 2 → scales.length (index.val + 1) ≤ 1 → scales.hessian ≤ 1 →
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index →
      diagonalDifference family.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2 →
      ‖centroidAsymmetry family.patchMotion time index‖ ≤ memory * scales.length (index.val + 1) ^ 2 →
      scales.length (index.val + 1) < momentRadius / (8 * (memory + 1)) →
      0 < (negativeHalfDiagonal family.patchMotion time index / positiveHalfDiagonal family.patchMotion time index).im →
      |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤ 1 / 4 →
      |deriv (referenceDilation scales family.patchMotion index) time| ≤
          12 * referenceOddForcingBudget scales (index.val + 1) internal memory bound ∧
        (|unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| < phaseRadius →
          |referencePhaseError scales family.patchMotion index time| ≤
            2 * phaseConstant * scales.omega (index.val + 1) *
              (|unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index|) +
            referenceOddForcingBudget scales (index.val + 1) internal memory bound) := by
  obtain ⟨internal, internalNonnegative, momentRadius, momentRadiusPositive, forcingEstimate⟩ :=
    exists_uniform_reference_odd_forcing_bound
  obtain ⟨phaseConstant, phaseConstantNonnegative, phaseRadius, phaseRadiusPositive, phaseEstimate⟩ :=
    exists_uniform_forced_point_phase_error_bound
  refine ⟨internal, internalNonnegative, momentRadius, momentRadiusPositive, phaseConstant, phaseConstantNonnegative,
    phaseRadius, phaseRadiusPositive, ?_⟩
  intro count family scales horizon time deformation memory bound evolution inside amplitudePositive frequencyBound ratioBound
    alphaPositive index pathInside material geometry control nonnegative small memoryNonnegative boundNonnegative deformationBound
    lengthBound hessianBound differenceLower differenceUpper asymmetryBound lengthSmall upper chartSmall
  let positive := positiveHalfDiagonal family.patchMotion time index
  let negative := negativeHalfDiagonal family.patchMotion time index
  let positions := fun patch => patchCentroid family.patchMotion time index patch
  let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
  let forcing := fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales family.patchMotion time index)
  let budget := referenceOddForcingBudget scales (index.val + 1) internal memory bound
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := scales.length_pos (index.val + 1)
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have budgetNonnegative : 0 ≤ budget := by dsimp only [budget, referenceOddForcingBudget]; positivity
  have chartIdentity : pointShapeChart positive negative =
      (unstableShape family.patchMotion time index, stableShape family.patchMotion time index) :=
    pointShapeChart_eq_paper_shape_of_upper family.patchMotion time index upper
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
  have noncollision := centrallySymmetricFourPoint_noncollision positiveNonzero negativeNonzero differenceNonzero sumNonzero
  have squareNonzero : star positive ^ 2 - star negative ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (by simpa only [star_add] using star_ne_zero.mpr sumNonzero)
      (by simpa only [star_sub] using star_ne_zero.mpr differenceNonzero)
  have momentSmall := reference_normalized_signed_moment_small scales family.patchMotion time index memoryNonnegative
    momentRadiusPositive differenceLower asymmetryBound lengthSmall
  have forcingBound : ‖forcing‖ / ‖positive‖ ≤ budget :=
    forcingEstimate evolution inside amplitudePositive frequencyBound ratioBound alphaPositive index geometry control nonnegative small
      memoryNonnegative boundNonnegative deformationBound lengthBound hessianBound differenceLower asymmetryBound momentSmall coherentSmall
  have differencePositive : 0 < diagonalDifference family.patchMotion time index :=
    (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le differenceLower
  have rateIdentity : scales.omega (index.val + 1) / referenceDilation scales family.patchMotion index time =
      coefficient / diagonalDifference family.patchMotion time index := by
    unfold referenceDilation coefficient
    field_simp
    <;> ring
  have rateBound : coefficient / diagonalDifference family.patchMotion time index ≤ 2 * scales.omega (index.val + 1) := by
    apply (div_le_iff₀ differencePositive).mpr
    dsimp only [coefficient]
    nlinarith [mul_le_mul_of_nonneg_left differenceLower omegaPositive.le]
  constructor
  · have equation := (family.centroid_diagonalDifference_hasDerivAt evolution inside index pathInside material noncollision normOrder).div_const
      (scales.length (index.val + 1) ^ 2)
    have derivativeIdentity : deriv (referenceDilation scales family.patchMotion index) time =
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
    have phaseIdentity := family.centroid_positive_phase_rate evolution inside index pathInside material noncollision normOrder
    have targetIdentity : referencePhaseError scales family.patchMotion index time =
        ((positivePointVelocity coefficient positive negative + forcing.1) / positive).im +
          coefficient / diagonalDifference family.patchMotion time index := by
      rw [referencePhaseError, rateIdentity, phaseIdentity]
      rw [add_div, Complex.add_im, positive_point_log_im_eq_rotation coefficient positiveNonzero negativeNonzero squareNonzero normOrder]
      rfl
    rw [targetIdentity]
    apply actual.trans
    apply add_le_add _ forcingBound
    have chartBound : ‖pointShapeChart positive negative‖ ≤
        |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| := by
      rw [chartIdentity, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _)
    calc
      _ ≤ phaseConstant * (2 * scales.omega (index.val + 1)) *
          (|unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index|) := by
        gcongr
        exact rateBound
      _ = _ := by ring

end EulerNonuniqueness.Paper
