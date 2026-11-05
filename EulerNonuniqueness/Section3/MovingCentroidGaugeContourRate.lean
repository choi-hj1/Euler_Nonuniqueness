import EulerNonuniqueness.Section3.CanonicalExteriorPrefixRecovery
import EulerNonuniqueness.Section3.MovingCentroidGaugeAngularCost
import EulerNonuniqueness.General.ContourRateBudget

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance movingContourRateCanonicalC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

open EulerNonuniqueness.Section6

theorem exists_uniform_actual_contour_rate_radius :
    ∃ radius > 0, ∃ constant ≥ 1,
    ∀ {count : ℕ} {configuration : FiniteContourConfiguration count}
      {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
      {initial : MovingContourState count}
      (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
        backwardHorizon forwardHorizon initial),
    (∀ index, initial.2.2 index = standardCircleBanach) → initial.1 = 0 → 0 < margin →
    ∀ horizon time distance weight mass control : ℝ,
    time ∈ Icc 0 horizon → horizon < forwardHorizon →
    (∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) →
    ∀ (index : Fin count) (positive : 0 < distance), 0 ≤ weight → 0 ≤ mass →
    configuration.density index ≠ 0 → 192 * (trajectory.movingFamily.patch index).radius ≤ distance →
    (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (trajectory.movingFamily.patch source).domain time,
      distance ≤ ‖(trajectory.movingFamily.patch index).center time - position‖) →
    (∫ position, inverseSquareVorticityWeight
      (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase index) time)
      ((trajectory.movingFamily.patch index).center time) position) ≤ weight →
    ‖(trajectory.curve time).2.2 index - standardCircleBanach‖ < radius →
    ‖diskNeutralCLM (trajectory.spectralCoordinate index time)‖ ≤ radius →
    ‖diskRelabelCurve (diskNeutralCLM (trajectory.spectralCoordinate index time)) 1 - standardCircleBanach‖ +
      ‖(trajectory.curve time).2.2 index - diskRelabelCurve (diskNeutralCLM (trajectory.spectralCoordinate index time)) 1‖ ≤ radius →
    weight / |configuration.density index| ≤ radius →
    contourAreaFunctional ((trajectory.curve time).2.2 index) = Real.pi →
    contourCentroidFunctional ((trajectory.curve time).2.2 index) = 0 →
    ‖diskPhysicalTransverseProjection (trajectory.spectralCoordinate index time)‖ ≤ control →
    weight / |configuration.density index| ≤ control → control ≤ 1 →
    ∃ velocity : PeriodicC1HolderHalf,
      HasDerivAt (fun current => diskNeutralCLM (trajectory.spectralCoordinate index current)) velocity time ∧
      (let relative := (trajectory.curve time).2.2 index -
        diskRelabelCurve (diskNeutralCLM (trajectory.spectralCoordinate index time)) 1
       let corrected := trajectory.movingFamily.canonicalExteriorAffineCoordinate index
        (diskNeutralCLM (trajectory.spectralCoordinate index time)) (configuration.density index) time
        ((trajectory.curve time).2.2 index)
       |configuration.density index| * ‖diskPhysicalTransverseProjection (diskNormalizedSpectralCoordinate corrected)‖ ^ 3 +
        weight * ‖relative‖ ^ 2 + weight * ((trajectory.movingFamily.patch index).radius / distance) * ‖relative‖ +
        (weight ^ 2 + mass * weight / distance ^ 2) / |configuration.density index| +
        (weight / |configuration.density index|) * ‖velocity‖ ≤
      constant * (|configuration.density index| * control ^ 3 + weight * control ^ 2 +
        weight * ((trajectory.movingFamily.patch index).radius / distance) * control +
        (weight ^ 2 + mass * weight / distance ^ 2) / |configuration.density index|)) := by
  obtain ⟨recoveryRadius, recoveryPositive, recoveryConstant, recoveryOne, recoveries⟩ :=
    FiniteMovingPatchFamily.canonicalExteriorAffineCoordinate_exists_uniform_prefix_recovery
  obtain ⟨costRadius, costPositive, costConstant, costOne, costs⟩ :=
    exists_uniform_spectral_angular_cost_radius
  let radius := min recoveryRadius costRadius
  let coefficient := recoveryConstant + costConstant + 1
  let constant := coefficient ^ 3 + coefficient ^ 2 + 2 * coefficient + 1
  have coefficientOne : 1 ≤ coefficient := by dsimp [coefficient]; linarith
  have recoveryLe : recoveryConstant ≤ coefficient := by dsimp [coefficient]; linarith
  have costLe : costConstant ≤ coefficient := by dsimp [coefficient]; linarith
  have constantOne : 1 ≤ constant := by
    have extra : 0 ≤ coefficient ^ 3 + coefficient ^ 2 + 2 * coefficient := by positivity
    dsimp only [constant]
    linarith
  refine ⟨radius, lt_min recoveryPositive costPositive, constant, constantOne, ?_⟩
  intro count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial trajectory
    initialCircles initialClock marginPositive horizon time distance weight mass control inside beforeFinal safe
    index positive weightNonnegative massNonnegative nonzero small separated weightBound dataSmall angularSmall
    shapeSmall frequencySmall area centered transverseBound epsilonBound controlOne
  have smallFour : 4 * (trajectory.movingFamily.patch index).radius ≤ distance :=
    by linarith [(trajectory.movingFamily.patch index).radius_positive]
  have recovered := recoveries trajectory.movingFamily index
    (diskNeutralCLM (trajectory.spectralCoordinate index time)) ((trajectory.curve time).2.2 index) rfl
    (angularSmall.trans (min_le_left _ _)) (diskNeutralCLM_real _) nonzero positive weightNonnegative
    smallFour separated weightBound (dataSmall.trans_le (min_le_left _ _)) (shapeSmall.trans (min_le_left _ _))
    (frequencySmall.trans (min_le_left _ _)) area centered transverseBound epsilonBound controlOne
  obtain ⟨velocity, derivative, cost⟩ := costs trajectory initialCircles initialClock marginPositive
    horizon time distance weight inside beforeFinal safe index positive weightNonnegative nonzero small separated
    weightBound (dataSmall.trans_le (min_le_right _ _))
  refine ⟨velocity, derivative, ?_⟩
  dsimp only
  generalize originalEq : diskPhysicalTransverseProjection (trajectory.spectralCoordinate index time) = original
    at cost transverseBound
  generalize relativeEq : (trajectory.curve time).2.2 index -
    diskRelabelCurve (diskNeutralCLM (trajectory.spectralCoordinate index time)) 1 = relative at recovered ⊢
  generalize correctedEq : diskPhysicalTransverseProjection (diskNormalizedSpectralCoordinate
    (trajectory.movingFamily.canonicalExteriorAffineCoordinate index
      (diskNeutralCLM (trajectory.spectralCoordinate index time)) (configuration.density index) time
      ((trajectory.curve time).2.2 index))) = corrected at recovered ⊢
  have controlNonnegative : 0 ≤ control := (norm_nonneg original).trans transverseBound
  have amplitudeNonnegative : 0 ≤ (weight ^ 2 + mass * weight / distance ^ 2) / |configuration.density index| := by positivity
  have amplitudeLower : weight ^ 2 / |configuration.density index| ≤
      (weight ^ 2 + mass * weight / distance ^ 2) / |configuration.density index| :=
    div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (abs_nonneg _)
  have costUpper : (weight / |configuration.density index|) * ‖velocity‖ ≤ coefficient *
      (weight * control ^ 2 + (weight ^ 2 + mass * weight / distance ^ 2) / |configuration.density index|) := by
    have first := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg original) transverseBound 2) weightNonnegative
    have second := (mul_le_mul_of_nonneg_left (transverseBound.trans controlOne)
      (div_nonneg (sq_nonneg weight) (abs_nonneg _))).trans (by simpa only [mul_one] using amplitudeLower)
    have bounded := cost.trans (mul_le_mul_of_nonneg_left (add_le_add first second) (by linarith : 0 ≤ costConstant))
    exact bounded.trans (mul_le_mul_of_nonneg_right costLe (by positivity))
  have relativeBound := recovered.1.trans (mul_le_mul_of_nonneg_right recoveryLe controlNonnegative)
  have correctedBound := recovered.2.trans (mul_le_mul_of_nonneg_right recoveryLe controlNonnegative)
  exact EulerNonuniqueness.General.contour_four_scale_rate_bound coefficientOne (abs_nonneg _)
    weightNonnegative (div_nonneg (trajectory.movingFamily.patch index).radius_positive.le positive.le)
    amplitudeNonnegative controlNonnegative (norm_nonneg _) (norm_nonneg _)
    correctedBound relativeBound costUpper

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
