import EulerNonuniqueness.Section3.DiskSpectralSelfBounds
import EulerNonuniqueness.Section3.DiskSpectralProjectedTrajectory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectralFrozenNeutralCoordinate_hasDerivAt
    {trajectory : ℝ → PeriodicC1HolderHalf} {time : ℝ} {forcing : PeriodicC1HolderHalf}
    (equation : HasDerivAt trajectory (diskSpectralTubularEulerField (trajectory time) + forcing) time) :
    HasDerivAt
      (fun current => EulerNonuniqueness.General.quadraticCoordinate
        (diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM (trajectory time))) 1
        (diskPhysicalTransverseProjection (trajectory current)))
      (diskRotatingDerivative (EulerNonuniqueness.General.quadraticCoordinate
          (diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM (trajectory time))) 1
          (diskPhysicalTransverseProjection (trajectory time))) +
        diskSpectralFrozenRemainder (trajectory time) forcing) time := by
  have actual := diskSpectralFrozenQuadraticCoordinate_hasDerivAt equation
  dsimp only at actual
  rw [diskSpectralMovingQuadraticCorrection_neutral_parameter]
  unfold diskSpectralFrozenRemainder diskSpectralProjectedRemainder
  dsimp only
  with_reducible exact actual

theorem diskSpectralNeutral_forcing_speed_le
    (parameter forcing : PeriodicC1HolderHalf) {constant : ℝ}
    (selfBound : ‖diskRelabelNeutralCLM (diskSpectralTubularEulerField parameter)‖ ≤
      constant * ‖diskPhysicalTransverseProjection parameter‖ ^ 2) :
    ‖diskRelabelNeutralCLM (diskSpectralTubularEulerField parameter) + diskRelabelNeutralCLM forcing‖ ≤
      constant * ‖diskPhysicalTransverseProjection parameter‖ ^ 2 + ‖diskRelabelNeutralCLM forcing‖ := by
  exact (norm_add_le (diskRelabelNeutralCLM (diskSpectralTubularEulerField parameter))
    (diskRelabelNeutralCLM forcing)).trans (add_le_add_right selfBound _)

end

end EulerNonuniqueness.Paper
