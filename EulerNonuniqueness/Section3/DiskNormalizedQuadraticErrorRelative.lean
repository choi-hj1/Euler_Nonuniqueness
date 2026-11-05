import EulerNonuniqueness.Section3.DiskNormalizedSpectralRelativeIncrement
import EulerNonuniqueness.Section3.DiskSpectralQuadraticObservableC11
import EulerNonuniqueness.General.OperatorPairEvaluation

noncomputable section

open Filter Metric Set
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance normalizedQuadraticErrorRelativeC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskNormalizedQuadraticError (data error : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  fderiv ℝ diskSpectralQuadraticObservable (diskNormalizedSpectralCoordinate data)
    (diskNormalizedSpectralError data error)

theorem diskNormalizedQuadraticError_exists_uniform_pair_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      (∀ data error : PeriodicC1HolderHalf, ‖data - standardCircleBanach‖ ≤ radius →
        ‖diskNormalizedQuadraticError data error‖ ≤ constant * ‖error‖) ∧
      ∀ first final firstError finalError : PeriodicC1HolderHalf,
      ‖first - standardCircleBanach‖ ≤ radius → ‖final - standardCircleBanach‖ ≤ radius →
      ‖diskNormalizedQuadraticError first firstError - diskNormalizedQuadraticError final finalError‖ ≤
        constant * (‖firstError - finalError‖ + ‖first - final‖ * ‖finalError‖) := by
  obtain ⟨normalRadius, normalPositive, normalConstant, normalOne, normals⟩ :=
    diskNormalizedSpectralError_exists_relative_ball
  obtain ⟨quadraticRadius, quadraticPositive, quadraticConstant, quadraticOne, quadraticAbsolute, quadraticRelative⟩ :=
    diskSpectralQuadraticObservable_exists_uniform_derivative_ball
  obtain ⟨coordinateConstant, coordinateNeighborhood, coordinateNear, coordinateLip⟩ :=
    diskNormalizedSpectralCoordinate_hasLipschitzDerivativeNear_circle.lipschitzNear
  obtain ⟨coordinateRadius, coordinatePositive, coordinateContained⟩ := Metric.mem_nhds_iff.mp coordinateNear
  have normalZero : diskNormalizedSpectralCoordinate standardCircleBanach = 0 := by
    simp only [diskNormalizedSpectralCoordinate, contourAreaCentroidNormalization_circle, diskPhysicalSpectralCoordinate_circle]
  have coordinateSmall : ∀ᶠ data in 𝓝 standardCircleBanach, ‖diskNormalizedSpectralCoordinate data‖ < quadraticRadius := by
    have actual := diskNormalizedSpectralCoordinate_hasLipschitzDerivativeNear_circle.lipschitzNear.continuousAt.norm
    apply actual.eventually (gt_mem_nhds ?_)
    simpa only [normalZero, norm_zero] using quadraticPositive
  obtain ⟨validRadius, validPositive, valid⟩ := Metric.eventually_nhds_iff.mp coordinateSmall
  let radius := min normalRadius (min (coordinateRadius / 2) (validRadius / 2))
  let constant := quadraticConstant * normalConstant +
    quadraticConstant * (coordinateConstant : ℝ) * normalConstant + 1
  have quadraticNonnegative : 0 ≤ quadraticConstant := by linarith
  have normalNonnegative : 0 ≤ normalConstant := by linarith
  have productNonnegative : 0 ≤ quadraticConstant * (coordinateConstant : ℝ) * normalConstant := by positivity
  have constantOne : 1 ≤ constant := by dsimp only [constant]; nlinarith
  have absoluteLe : quadraticConstant * normalConstant ≤ constant := by dsimp only [constant]; linarith
  have secondLe : quadraticConstant * normalConstant + quadraticConstant * (coordinateConstant : ℝ) * normalConstant ≤ constant := by
    dsimp only [constant]
    linarith
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have within {data : PeriodicC1HolderHalf} (inside : ‖data - standardCircleBanach‖ ≤ radius) :
      ‖data - standardCircleBanach‖ ≤ normalRadius ∧ data ∈ coordinateNeighborhood ∧
        ‖diskNormalizedSpectralCoordinate data‖ ≤ quadraticRadius := by
    refine ⟨inside.trans (min_le_left _ _), coordinateContained ?_, (valid ?_).le⟩
    · rw [mem_ball, dist_eq_norm]
      exact (inside.trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (half_lt_self coordinatePositive)
    · rw [dist_eq_norm]
      exact (inside.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (half_lt_self validPositive)
  have normalBound (data error : PeriodicC1HolderHalf) (inside : ‖data - standardCircleBanach‖ ≤ radius) :
      ‖diskNormalizedSpectralError data error‖ ≤ normalConstant * ‖error‖ := by
    have actual := normals data data error 0 (within inside).1 (within inside).1
    simpa only [diskNormalizedSpectralError, map_zero, sub_zero, sub_self, norm_zero, zero_mul, add_zero] using actual
  refine ⟨radius, radiusPositive, constant, constantOne, ?_, ?_⟩
  · intro data error inside
    have operatorBound := (quadraticAbsolute _ (within inside).2.2).2
    have applied := (fderiv ℝ diskSpectralQuadraticObservable (diskNormalizedSpectralCoordinate data)).le_opNorm
      (diskNormalizedSpectralError data error)
    have bounded := applied.trans (mul_le_mul operatorBound (normalBound data error inside) (norm_nonneg _) quadraticNonnegative)
    have scalar := mul_le_mul_of_nonneg_right absoluteLe (norm_nonneg error)
    exact (bounded.trans_eq (by ring)).trans scalar
  · intro first final firstError finalError firstInside finalInside
    have firstWithin := within firstInside
    have finalWithin := within finalInside
    have firstOperator := (quadraticAbsolute _ firstWithin.2.2).2
    have coordinatePair := coordinateLip.norm_sub_le firstWithin.2.1 finalWithin.2.1
    have operatorPair := (quadraticRelative _ _ firstWithin.2.2 finalWithin.2.2).trans
      (mul_le_mul_of_nonneg_left coordinatePair quadraticNonnegative)
    have errorPair := normals first final firstError finalError firstWithin.1 finalWithin.1
    have errorFinal := normalBound final finalError finalInside
    have applied := EulerNonuniqueness.General.norm_operator_apply_difference_le
      (fderiv ℝ diskSpectralQuadraticObservable (diskNormalizedSpectralCoordinate first))
      (fderiv ℝ diskSpectralQuadraticObservable (diskNormalizedSpectralCoordinate final))
      (diskNormalizedSpectralError first firstError) (diskNormalizedSpectralError final finalError)
    have bounded := applied.trans (add_le_add
      (mul_le_mul firstOperator errorPair (norm_nonneg _) quadraticNonnegative)
      (mul_le_mul operatorPair errorFinal (norm_nonneg _) (by positivity)))
    have scalar := mul_le_mul_of_nonneg_right secondLe
      (by positivity : 0 ≤ ‖firstError - finalError‖ + ‖first - final‖ * ‖finalError‖)
    have leftover : 0 ≤ quadraticConstant * (coordinateConstant : ℝ) * normalConstant * ‖firstError - finalError‖ := by positivity
    have combined : quadraticConstant * (normalConstant * (‖firstError - finalError‖ + ‖first - final‖ * ‖finalError‖)) +
        (quadraticConstant * ((coordinateConstant : ℝ) * ‖first - final‖)) * (normalConstant * ‖finalError‖) ≤
        (quadraticConstant * normalConstant + quadraticConstant * (coordinateConstant : ℝ) * normalConstant) *
          (‖firstError - finalError‖ + ‖first - final‖ * ‖finalError‖) := by
      nlinarith only [leftover]
    exact (bounded.trans combined).trans scalar

end EulerNonuniqueness.Paper
