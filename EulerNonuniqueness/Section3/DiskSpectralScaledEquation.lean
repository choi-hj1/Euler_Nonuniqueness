import EulerNonuniqueness.Section3.DiskSpectralMovingCoordinateEquation
import EulerNonuniqueness.General.ScaledQuadraticFamilyDerivative

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

def diskSpectralScaledFrozenRemainder (frequency : ℝ) (parameter forcing : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf :=
  let value := diskPhysicalTransverseProjection parameter
  let remainder := frequency • diskSpectralProjectedRemainder parameter + diskPhysicalTransverseProjection forcing
  remainder - (diskSpectralMovingQuadraticCorrection parameter
      ((frequency • diskSpectralProjectedQuadratic parameter) value value + remainder) value +
    diskSpectralMovingQuadraticCorrection parameter value
      ((frequency • diskSpectralProjectedQuadratic parameter) value value + remainder))

theorem diskSpectralScaledFrozenCoordinate_hasDerivAt
    (frequency : ℝ) {trajectory : ℝ → PeriodicC1HolderHalf} {time : ℝ} {forcing : PeriodicC1HolderHalf}
    (equation : HasDerivAt trajectory (frequency • diskSpectralTubularEulerField (trajectory time) + forcing) time) :
    HasDerivAt
      (fun current => EulerNonuniqueness.General.quadraticCoordinate
        (diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM (trajectory time))) 1
        (diskPhysicalTransverseProjection (trajectory current)))
      ((frequency • diskRotatingDerivative) (EulerNonuniqueness.General.quadraticCoordinate
          (diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM (trajectory time))) 1
          (diskPhysicalTransverseProjection (trajectory time))) +
        diskSpectralScaledFrozenRemainder frequency (trajectory time) forcing) time := by
  with_reducible
    have actual := EulerNonuniqueness.General.projected_quadratic_family_scaled_hasDerivAt
      (Space := PeriodicC1HolderHalf) diskPhysicalTransverseProjection diskRotatingDerivative
      diskSpectralProjectedQuadratic diskSpectralMovingQuadraticCorrection diskSpectralTubularEulerField
      diskSpectralMovingQuadraticCorrection_homological frequency equation
    dsimp only at actual
    have residual := EulerNonuniqueness.General.scaled_projected_family_residual_identity
      (Space := PeriodicC1HolderHalf) diskPhysicalTransverseProjection diskRotatingDerivative
      diskSpectralProjectedQuadratic diskSpectralTubularEulerField frequency (trajectory time)
    rw [residual] at actual
    rw [diskSpectralMovingQuadraticCorrection_neutral_parameter]
    unfold diskSpectralScaledFrozenRemainder diskSpectralProjectedRemainder
    dsimp only
    exact actual

theorem diskSpectralScaledNeutral_trajectory_hasDerivAt
    (frequency : ℝ) {trajectory : ℝ → PeriodicC1HolderHalf} {time : ℝ} {forcing : PeriodicC1HolderHalf}
    (equation : HasDerivAt trajectory (frequency • diskSpectralTubularEulerField (trajectory time) + forcing) time) :
    HasDerivAt (fun current => diskRelabelNeutralCLM (trajectory current))
      (frequency • diskRelabelNeutralCLM (diskSpectralTubularEulerField (trajectory time)) +
        diskRelabelNeutralCLM forcing) time := by
  with_reducible
    have actual := EulerNonuniqueness.General.linear_projected_field_hasDerivAt
      diskRelabelNeutralCLM (fun value => frequency • diskSpectralTubularEulerField value) equation
    simpa only [map_smul] using actual

end

end EulerNonuniqueness.Paper
