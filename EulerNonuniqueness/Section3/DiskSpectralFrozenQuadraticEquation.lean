import EulerNonuniqueness.Section3.DiskSpectralAreaCubic
import EulerNonuniqueness.General.ProjectedQuadraticFamilyDerivative

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

def diskSpectralProjectedRemainder (increment : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskPhysicalTransverseProjection (diskSpectralTubularEulerField increment) -
    diskRotatingDerivative (diskPhysicalTransverseProjection increment) -
    diskSpectralProjectedQuadratic increment (diskPhysicalTransverseProjection increment)
      (diskPhysicalTransverseProjection increment)

theorem diskSpectralMovingQuadraticCorrection_neutral_parameter (parameter : PeriodicC1HolderHalf) :
    diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM parameter) =
      diskSpectralMovingQuadraticCorrection parameter := by
  unfold diskSpectralMovingQuadraticCorrection diskSpectralProjectedQuadratic
  rw [diskSpectralFiberQuadraticBilinear_neutral_parameter]

theorem diskSpectralFrozenQuadraticCoordinate_hasDerivAt
    {trajectory : ℝ → PeriodicC1HolderHalf} {time : ℝ} {forcing : PeriodicC1HolderHalf}
    (equation : HasDerivAt trajectory (diskSpectralTubularEulerField (trajectory time) + forcing) time) :
    let value := diskPhysicalTransverseProjection (trajectory time)
    let remainder := diskPhysicalTransverseProjection (diskSpectralTubularEulerField (trajectory time)) -
      diskRotatingDerivative value - diskSpectralProjectedQuadratic (trajectory time) value value +
      diskPhysicalTransverseProjection forcing
    HasDerivAt
      (fun current => EulerNonuniqueness.General.quadraticCoordinate
        (diskSpectralMovingQuadraticCorrection (trajectory time)) 1 (diskPhysicalTransverseProjection (trajectory current)))
      (diskRotatingDerivative (EulerNonuniqueness.General.quadraticCoordinate
          (diskSpectralMovingQuadraticCorrection (trajectory time)) 1 value) +
        (remainder - (diskSpectralMovingQuadraticCorrection (trajectory time)
            (diskSpectralProjectedQuadratic (trajectory time) value value + remainder) value +
          diskSpectralMovingQuadraticCorrection (trajectory time) value
            (diskSpectralProjectedQuadratic (trajectory time) value value + remainder)))) time := by
  with_reducible
    exact EulerNonuniqueness.General.projected_quadratic_family_hasDerivAt
      (Space := PeriodicC1HolderHalf) diskPhysicalTransverseProjection diskRotatingDerivative
      diskSpectralProjectedQuadratic diskSpectralMovingQuadraticCorrection diskSpectralTubularEulerField
      diskSpectralMovingQuadraticCorrection_homological equation

end

end EulerNonuniqueness.Paper
