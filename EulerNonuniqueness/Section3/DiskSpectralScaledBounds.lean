import EulerNonuniqueness.Section3.DiskSpectralScaledEquation
import EulerNonuniqueness.General.ScaledFrozenQuadraticCubicBound

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectralScaledFrozenRemainder_norm_le
    (frequency : ℝ) (parameter forcing : PeriodicC1HolderHalf)
    {remainderConstant bilinearConstant correctionConstant : ℝ}
    (remainderNonnegative : 0 ≤ remainderConstant) (bilinearNonnegative : 0 ≤ bilinearConstant)
    (correctionNonnegative : 0 ≤ correctionConstant)
    (remainderBound : ‖diskSpectralProjectedRemainder parameter‖ ≤
      remainderConstant * ‖diskPhysicalTransverseProjection parameter‖ ^ 3)
    (bilinearBound : ‖diskSpectralFiberQuadraticBilinear parameter‖ ≤ bilinearConstant)
    (correctionBound : ‖diskSpectralMovingQuadraticCorrection parameter‖ ≤ correctionConstant)
    (small : ‖diskPhysicalTransverseProjection parameter‖ ≤ 1) :
    ‖diskSpectralScaledFrozenRemainder frequency parameter forcing‖ ≤
      (|frequency| * (remainderConstant + 2 * correctionConstant *
        (‖diskPhysicalTransverseProjection‖ ^ 3 * bilinearConstant + remainderConstant))) *
          ‖diskPhysicalTransverseProjection parameter‖ ^ 3 +
      (1 + 2 * correctionConstant * ‖diskPhysicalTransverseProjection parameter‖) *
        ‖diskPhysicalTransverseProjection forcing‖ := by
  have quadraticBound : ‖diskSpectralProjectedQuadratic parameter‖ ≤
      ‖diskPhysicalTransverseProjection‖ ^ 3 * bilinearConstant :=
    (diskSpectralProjectedQuadratic_norm_le parameter).trans
      (mul_le_mul_of_nonneg_left bilinearBound (by positivity))
  unfold diskSpectralScaledFrozenRemainder
  with_reducible
    exact EulerNonuniqueness.General.norm_scaled_frozen_quadratic_remainder_le
      (Space := PeriodicC1HolderHalf) (diskSpectralProjectedQuadratic parameter)
      (diskSpectralMovingQuadraticCorrection parameter) frequency (diskPhysicalTransverseProjection parameter)
      (diskSpectralProjectedRemainder parameter) (diskPhysicalTransverseProjection forcing)
      remainderNonnegative (by positivity) correctionNonnegative quadraticBound correctionBound small remainderBound

theorem diskSpectralScaledNeutral_forcing_speed_le
    (frequency : ℝ) (parameter forcing : PeriodicC1HolderHalf) {constant : ℝ}
    (selfBound : ‖diskRelabelNeutralCLM (diskSpectralTubularEulerField parameter)‖ ≤
      constant * ‖diskPhysicalTransverseProjection parameter‖ ^ 2) :
    ‖frequency • diskRelabelNeutralCLM (diskSpectralTubularEulerField parameter) + diskRelabelNeutralCLM forcing‖ ≤
      (|frequency| * constant) * ‖diskPhysicalTransverseProjection parameter‖ ^ 2 +
        ‖diskRelabelNeutralCLM forcing‖ := by
  apply (norm_add_le (frequency • diskRelabelNeutralCLM (diskSpectralTubularEulerField parameter))
    (diskRelabelNeutralCLM forcing)).trans
  have scaledNorm :
      ‖frequency • diskRelabelNeutralCLM (diskSpectralTubularEulerField parameter)‖ =
        |frequency| * ‖diskRelabelNeutralCLM (diskSpectralTubularEulerField parameter)‖ := by
    with_reducible
      simpa only [Real.norm_eq_abs] using norm_smul frequency
        (diskRelabelNeutralCLM (diskSpectralTubularEulerField parameter))
  rw [scaledNorm]
  exact add_le_add_right
    ((mul_le_mul_of_nonneg_left selfBound (abs_nonneg _)).trans_eq (by ring)) _

end

end EulerNonuniqueness.Paper
