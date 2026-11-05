import EulerNonuniqueness.Section3.CanonicalExteriorCommonMaterialField
import EulerNonuniqueness.Section3.CanonicalExteriorCommonNormalizedBounds
import EulerNonuniqueness.Section3.DiskSpectralQuadraticObservableEvolution

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd

def canonicalExteriorCommonQuadraticCoordinate {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time : ℝ) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskSpectralQuadraticObservable (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time data)

def canonicalExteriorCommonQuadraticSourceOperator {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time : ℝ) (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (fderiv ℝ diskSpectralQuadraticObservable
    (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time data)).comp
      (family.canonicalExteriorCommonNormalizedPhysicalDerivative index frequency time data)

theorem canonicalExteriorCommonQuadraticCoordinate_exists_material_evolution_ball :
    ∃ physicalRadius > 0, ∃ spectralRadius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        {curve : ℝ → PeriodicC1HolderHalf} {frequency time : ℝ} (residual sourceDifference : PeriodicC1HolderHalf),
      ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time) - standardCircleBanach‖ ≤ physicalRadius →
      ‖family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (curve time)‖ ≤ spectralRadius →
      HasDerivAt (fun current => family.canonicalExteriorCommonPhysicalCoordinate index frequency current (curve current))
        (frequency • diskEulerRotatingField (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time)) +
          residual + family.canonicalExteriorCommonPhysicalDerivative index frequency time (curve time) sourceDifference) time →
      diskSpectralTubularArea (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (curve time)) = Real.pi ∧
      HasDerivAt (fun current => family.canonicalExteriorCommonQuadraticCoordinate index frequency current (curve current))
        (frequency • diskRotatingDerivative (family.canonicalExteriorCommonQuadraticCoordinate index frequency time (curve time)) +
          frequency • diskSpectralMovingSelfRemainder
            (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (curve time)) +
          fderiv ℝ diskSpectralQuadraticObservable
            (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (curve time))
            (diskNormalizedSpectralError
              (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time)) residual) +
          family.canonicalExteriorCommonQuadraticSourceOperator index frequency time (curve time) sourceDifference) time ∧
      ‖fderiv ℝ diskSpectralQuadraticObservable
        (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (curve time))
        (diskNormalizedSpectralError
          (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time)) residual)‖ ≤ constant * ‖residual‖ ∧
      ‖family.canonicalExteriorCommonQuadraticSourceOperator index frequency time (curve time)‖ ≤
        constant * ‖family.canonicalExteriorCommonPhysicalDerivative index frequency time (curve time)‖ := by
  obtain ⟨materialRadius, materialPositive, materialConstant, materialOne, materialEvolution⟩ :=
    canonicalExteriorCommonNormalizedPhysicalCoordinate_exists_material_evolution_ball
  obtain ⟨normalizedRadius, normalizedPositive, normalizedConstant, normalizedOne, normalizedBound⟩ :=
    canonicalExteriorCommonNormalizedPhysicalDerivative_exists_norm_ball
  obtain ⟨quadraticRadius, quadraticPositive, _, _, quadraticEvolution⟩ :=
    diskSpectralQuadraticObservable_exists_forced_evolution_ball
  obtain ⟨derivativeRadius, derivativePositive, derivativeConstant, derivativeOne, quadraticDerivatives, _⟩ :=
    diskSpectralQuadraticObservable_exists_uniform_derivative_ball
  let constant := derivativeConstant * materialConstant + derivativeConstant * normalizedConstant + 1
  have materialNonnegative : 0 ≤ materialConstant := by linarith
  have derivativeNonnegative : 0 ≤ derivativeConstant := by linarith
  have normalizedNonnegative : 0 ≤ normalizedConstant := by linarith
  have constantOne : 1 ≤ constant := by
    have firstNonnegative : 0 ≤ derivativeConstant * materialConstant := by positivity
    have secondNonnegative : 0 ≤ derivativeConstant * normalizedConstant := by positivity
    dsimp only [constant]
    linarith
  refine ⟨min materialRadius normalizedRadius, lt_min materialPositive normalizedPositive,
    min quadraticRadius derivativeRadius, lt_min quadraticPositive derivativePositive, constant, constantOne, ?_⟩
  intro count family index curve frequency time residual sourceDifference physicalInside spectralInside equation
  have normalized := materialEvolution family index residual sourceDifference (physicalInside.trans (min_le_left _ _)) equation
  let normalizedCurve := fun current => family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency current (curve current)
  let normalizedForcing := diskNormalizedSpectralError
    (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time)) residual +
      family.canonicalExteriorCommonNormalizedPhysicalDerivative index frequency time (curve time) sourceDifference
  have normalizedEquation : HasDerivAt normalizedCurve
      (frequency • diskSpectralTubularEulerField (normalizedCurve time) + normalizedForcing) time := by
    with_reducible_and_instances
      simpa only [normalizedCurve, normalizedForcing, add_assoc] using normalized.2.1
  have quadratic := quadraticEvolution
    (curve := normalizedCurve)
    (frequency := frequency) (time := time)
    normalizedForcing
    (spectralInside.trans (min_le_left _ _))
    normalizedEquation
  have derivativeBound := (quadraticDerivatives
    (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (curve time))
      (spectralInside.trans (min_le_right _ _))).2
  have normalizedOperator := normalizedBound family index frequency time (curve time)
    (physicalInside.trans (min_le_right _ _))
  have materialLe : derivativeConstant * materialConstant ≤ constant := by
    have nonnegative : 0 ≤ derivativeConstant * normalizedConstant := by positivity
    dsimp only [constant]
    linarith
  have sourceLe : derivativeConstant * normalizedConstant ≤ constant := by
    have nonnegative : 0 ≤ derivativeConstant * materialConstant := by positivity
    dsimp only [constant]
    linarith
  refine ⟨normalized.1, ?_, ?_, ?_⟩
  · with_reducible_and_instances
      simpa only [canonicalExteriorCommonQuadraticCoordinate, canonicalExteriorCommonQuadraticSourceOperator,
        normalizedCurve, normalizedForcing, ContinuousLinearMap.comp_apply, map_add, add_assoc] using quadratic.1
  · have applied := (fderiv ℝ diskSpectralQuadraticObservable
      (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (curve time))).le_opNorm
        (diskNormalizedSpectralError (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time)) residual)
    have bounded := applied.trans (mul_le_mul derivativeBound normalized.2.2 (norm_nonneg _) derivativeNonnegative)
    have scalar := mul_le_mul_of_nonneg_right materialLe (norm_nonneg residual)
    exact (bounded.trans_eq (by ring)).trans scalar
  · have composed := ContinuousLinearMap.opNorm_comp_le
      (fderiv ℝ diskSpectralQuadraticObservable
        (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (curve time)))
      (family.canonicalExteriorCommonNormalizedPhysicalDerivative index frequency time (curve time))
    have bounded := composed.trans (mul_le_mul derivativeBound normalizedOperator (norm_nonneg _) derivativeNonnegative)
    have scalar := mul_le_mul_of_nonneg_right sourceLe
      (norm_nonneg (family.canonicalExteriorCommonPhysicalDerivative index frequency time (curve time)))
    exact (bounded.trans_eq (by ring)).trans scalar

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
