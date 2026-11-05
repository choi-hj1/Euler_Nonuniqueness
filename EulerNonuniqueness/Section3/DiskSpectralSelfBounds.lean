import EulerNonuniqueness.Section3.DiskSpectralProjectedBounds
import EulerNonuniqueness.Section3.DiskSpectralFrozenQuadraticEquation
import EulerNonuniqueness.General.FrozenQuadraticCubicRemainderBound

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter Metric
open scoped Topology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectral_exists_uniform_projected_self_bounds :
    ∃ radius > 0, ∃ remainderConstant ≥ 0, ∃ bilinearConstant ≥ 0, ∃ correctionConstant ≥ 0,
    ∃ neutralConstant ≥ 0,
    ∀ parameter : PeriodicC1HolderHalf,
      ‖diskRelabelNeutralCLM parameter‖ + ‖parameter - diskRelabelNeutralCLM parameter‖ ≤ radius →
      diskSpectralTubularArea parameter = Real.pi →
      ‖diskSpectralProjectedRemainder parameter‖ ≤
          remainderConstant * ‖diskPhysicalTransverseProjection parameter‖ ^ 3 ∧
      ‖diskSpectralFiberQuadraticBilinear parameter‖ ≤ bilinearConstant ∧
      ‖diskSpectralMovingQuadraticCorrection parameter‖ ≤ correctionConstant ∧
      (‖diskPhysicalTransverseProjection parameter‖ ≤ 1 →
        ‖diskRelabelNeutralCLM (diskSpectralTubularEulerField parameter)‖ ≤
          neutralConstant * ‖diskPhysicalTransverseProjection parameter‖ ^ 2) := by
  obtain ⟨areaRadius, areaPositive, rawConstant, rawNonnegative, areaBound⟩ :=
    diskSpectralTubularEulerField_exists_area_transverse_cubic
  obtain ⟨bilinearConstant, bilinearNonnegative, bilinearBound⟩ :=
    diskSpectralFiberQuadraticBilinear_exists_uniform_norm_bound
  obtain ⟨correctionConstant, correctionNonnegative, correctionBound⟩ :=
    diskSpectralMovingQuadraticCorrection_exists_uniform_norm_bound
  obtain ⟨boundRadius, boundPositive, contained⟩ :=
    Metric.mem_nhds_iff.mp (bilinearBound.and correctionBound)
  refine ⟨min areaRadius (boundRadius / 2), lt_min areaPositive (by positivity),
    ‖diskPhysicalTransverseProjection‖ * rawConstant, by positivity,
    bilinearConstant, bilinearNonnegative, correctionConstant, correctionNonnegative,
    ‖diskRelabelNeutralCLM‖ * (rawConstant + bilinearConstant), by positivity, ?_⟩
  intro parameter inside area
  have parameterNorm : ‖parameter‖ ≤
      ‖diskRelabelNeutralCLM parameter‖ + ‖parameter - diskRelabelNeutralCLM parameter‖ := by
    have identity : diskRelabelNeutralCLM parameter + (parameter - diskRelabelNeutralCLM parameter) = parameter := by abel
    simpa only [identity] using norm_add_le (diskRelabelNeutralCLM parameter) (parameter - diskRelabelNeutralCLM parameter)
  have bounded : ‖diskSpectralFiberQuadraticBilinear parameter‖ ≤ bilinearConstant ∧
      ‖diskSpectralMovingQuadraticCorrection parameter‖ ≤ correctionConstant :=
    contained (show parameter ∈ ball (0 : PeriodicC1HolderHalf) boundRadius by
    rw [Metric.mem_ball]
    have distance : dist parameter (0 : PeriodicC1HolderHalf) = ‖parameter‖ := by
      with_reducible exact dist_zero_right parameter
    rw [distance]
    have small := inside.trans (min_le_right _ _)
    linarith)
  have raw := areaBound parameter (inside.trans (min_le_left _ _)) area
  dsimp only at raw
  rw [diskSpectralRelative_transverse] at raw
  refine ⟨?_, bounded.1, bounded.2, ?_⟩
  · have fixed : diskPhysicalTransverseProjection (diskPhysicalTransverseProjection parameter) =
        diskPhysicalTransverseProjection parameter := by
      exact congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => linear parameter)
        diskPhysicalTransverseProjection_idempotent
    have projected := diskSpectralProjected_cubic_error_le (diskSpectralTubularEulerField parameter)
      parameter (diskPhysicalTransverseProjection parameter) fixed raw
    unfold diskSpectralProjectedRemainder
    with_reducible exact projected
  · intro small
    with_reducible
      exact diskSpectralNeutral_quadratic_error_le (diskSpectralTubularEulerField parameter) parameter
        (diskPhysicalTransverseProjection parameter) rawNonnegative bilinearNonnegative small bounded.1 raw

theorem diskSpectralNeutral_self_bound
    (parameter : PeriodicC1HolderHalf) {rawConstant bilinearConstant : ℝ}
    (rawNonnegative : 0 ≤ rawConstant) (bilinearNonnegative : 0 ≤ bilinearConstant)
    (small : ‖diskPhysicalTransverseProjection parameter‖ ≤ 1)
    (bounded : ‖diskSpectralFiberQuadraticBilinear parameter‖ ≤ bilinearConstant)
    (raw : ‖diskSpectralTubularEulerField parameter -
      diskRotatingDerivative (diskPhysicalTransverseProjection parameter) -
      diskSpectralFiberQuadraticBilinear parameter (diskPhysicalTransverseProjection parameter)
        (diskPhysicalTransverseProjection parameter)‖ ≤
          rawConstant * ‖diskPhysicalTransverseProjection parameter‖ ^ 3) :
    ‖diskRelabelNeutralCLM (diskSpectralTubularEulerField parameter)‖ ≤
      (‖diskRelabelNeutralCLM‖ * (rawConstant + bilinearConstant)) *
        ‖diskPhysicalTransverseProjection parameter‖ ^ 2 := by
  with_reducible
    exact diskSpectralNeutral_quadratic_error_le (diskSpectralTubularEulerField parameter) parameter
      (diskPhysicalTransverseProjection parameter) rawNonnegative bilinearNonnegative small bounded raw

def diskSpectralFrozenRemainder (parameter forcing : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  let value := diskPhysicalTransverseProjection parameter
  let remainder := diskSpectralProjectedRemainder parameter + diskPhysicalTransverseProjection forcing
  remainder - (diskSpectralMovingQuadraticCorrection parameter
      (diskSpectralProjectedQuadratic parameter value value + remainder) value +
    diskSpectralMovingQuadraticCorrection parameter value
      (diskSpectralProjectedQuadratic parameter value value + remainder))

theorem diskSpectralFrozenRemainder_norm_le
    (parameter forcing : PeriodicC1HolderHalf) {remainderConstant bilinearConstant correctionConstant : ℝ}
    (remainderNonnegative : 0 ≤ remainderConstant) (bilinearNonnegative : 0 ≤ bilinearConstant)
    (correctionNonnegative : 0 ≤ correctionConstant)
    (remainderBound : ‖diskSpectralProjectedRemainder parameter‖ ≤
      remainderConstant * ‖diskPhysicalTransverseProjection parameter‖ ^ 3)
    (bilinearBound : ‖diskSpectralFiberQuadraticBilinear parameter‖ ≤ bilinearConstant)
    (correctionBound : ‖diskSpectralMovingQuadraticCorrection parameter‖ ≤ correctionConstant)
    (small : ‖diskPhysicalTransverseProjection parameter‖ ≤ 1) :
    ‖diskSpectralFrozenRemainder parameter forcing‖ ≤
      (remainderConstant + 2 * correctionConstant *
        (‖diskPhysicalTransverseProjection‖ ^ 3 * bilinearConstant + remainderConstant)) *
          ‖diskPhysicalTransverseProjection parameter‖ ^ 3 +
      (1 + 2 * correctionConstant * ‖diskPhysicalTransverseProjection parameter‖) *
        ‖diskPhysicalTransverseProjection forcing‖ := by
  have quadraticBound : ‖diskSpectralProjectedQuadratic parameter‖ ≤
      ‖diskPhysicalTransverseProjection‖ ^ 3 * bilinearConstant :=
    (diskSpectralProjectedQuadratic_norm_le parameter).trans
      (mul_le_mul_of_nonneg_left bilinearBound (by positivity))
  unfold diskSpectralFrozenRemainder
  with_reducible
    exact EulerNonuniqueness.General.norm_frozen_quadratic_remainder_le
      (Space := PeriodicC1HolderHalf) (diskSpectralProjectedQuadratic parameter)
      (diskSpectralMovingQuadraticCorrection parameter) (diskPhysicalTransverseProjection parameter)
      (diskSpectralProjectedRemainder parameter) (diskPhysicalTransverseProjection forcing)
      remainderNonnegative (by positivity) correctionNonnegative quadraticBound correctionBound small remainderBound

end

end EulerNonuniqueness.Paper
