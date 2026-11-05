import EulerNonuniqueness.Section3.DiskSpectralAreaCubic
import EulerNonuniqueness.General.LinearProjectedFieldDerivative

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectralNeutral_trajectory_hasDerivAt
    {trajectory : ℝ → PeriodicC1HolderHalf} {time : ℝ} {forcing : PeriodicC1HolderHalf}
    (equation : HasDerivAt trajectory (diskSpectralTubularEulerField (trajectory time) + forcing) time) :
    HasDerivAt (fun current => diskRelabelNeutralCLM (trajectory current))
      (diskRelabelNeutralCLM (diskSpectralTubularEulerField (trajectory time)) +
        diskRelabelNeutralCLM forcing) time := by
  exact EulerNonuniqueness.General.linear_projected_field_hasDerivAt
    diskRelabelNeutralCLM diskSpectralTubularEulerField equation

theorem diskSpectralTransverse_trajectory_hasDerivAt
    {trajectory : ℝ → PeriodicC1HolderHalf} {time : ℝ} {forcing : PeriodicC1HolderHalf}
    (equation : HasDerivAt trajectory (diskSpectralTubularEulerField (trajectory time) + forcing) time) :
    HasDerivAt (fun current => diskPhysicalTransverseProjection (trajectory current))
      (diskPhysicalTransverseProjection (diskSpectralTubularEulerField (trajectory time)) +
        diskPhysicalTransverseProjection forcing) time := by
  exact EulerNonuniqueness.General.linear_projected_field_hasDerivAt
    diskPhysicalTransverseProjection diskSpectralTubularEulerField equation

end

end EulerNonuniqueness.Paper
