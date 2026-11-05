import EulerNonuniqueness.Section3.DiskMovingQuadraticTaylor
import EulerNonuniqueness.Section3.DiskSpectralFiberAlgebra
import EulerNonuniqueness.Section3.DiskPhysicalResonance
import EulerNonuniqueness.General.ProjectedQuadraticResonance
import EulerNonuniqueness.General.QuadraticHomologicalEvaluation

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

def diskSpectralFiberQuadraticBilinear (parameter : PeriodicC1HolderHalf) :
    EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.bilinearPostcompose (Space := PeriodicC1HolderHalf)
    (Ring.inverse (diskChartedSpectralCoordinates parameter))
    ((diskMovingQuadraticBilinear (diskRelabelNeutralCLM parameter)).bilinearComp
      (diskChartedSpectralCoordinates parameter) (diskChartedSpectralCoordinates parameter))

theorem diskSpectralFiberQuadraticBilinear_apply (parameter first second : PeriodicC1HolderHalf) :
    diskSpectralFiberQuadraticBilinear parameter first second =
      Ring.inverse (diskChartedSpectralCoordinates parameter)
        (diskMovingQuadraticBilinear (diskRelabelNeutralCLM parameter)
          (diskChartedSpectralCoordinates parameter first) (diskChartedSpectralCoordinates parameter second)) := rfl

theorem diskSpectralFiberQuadraticBilinear_neutral_parameter (parameter : PeriodicC1HolderHalf) :
    diskSpectralFiberQuadraticBilinear (diskRelabelNeutralCLM parameter) =
      diskSpectralFiberQuadraticBilinear parameter := by
  unfold diskSpectralFiberQuadraticBilinear
  rw [diskRelabelNeutralCLM_idempotent, diskChartedSpectralCoordinates_neutral_parameter]

def diskSpectralProjectedQuadratic (parameter : PeriodicC1HolderHalf) :
    EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.projectedQuadratic (Space := PeriodicC1HolderHalf)
    diskPhysicalTransverseProjection (diskSpectralFiberQuadraticBilinear parameter)

def diskSpectralMovingQuadraticCorrection (parameter : PeriodicC1HolderHalf) :
    EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.quadraticHomologicalSolution (Space := PeriodicC1HolderHalf)
    diskPhysicalGroup (4 * Real.pi) (diskSpectralProjectedQuadratic parameter)

theorem diskSpectralProjectedQuadratic_resonance_zero (parameter : PeriodicC1HolderHalf) :
    EulerNonuniqueness.General.quadraticResonance (Space := PeriodicC1HolderHalf)
      diskPhysicalGroup (4 * Real.pi) (diskSpectralProjectedQuadratic parameter) = 0 := by
  unfold diskSpectralProjectedQuadratic
  rw [show 4 * Real.pi = 2 * (2 * Real.pi) by ring]
  with_reducible
    exact EulerNonuniqueness.General.projectedQuadratic_resonance_zero (Space := PeriodicC1HolderHalf)
      diskPhysicalGroup diskRotatingDerivative diskPhysicalTransverseProjection
      diskPhysicalGroup_zero diskPhysicalGroup_add diskPhysicalGroup_generator
      diskPhysicalTransverseProjection_idempotent diskPhysicalTransverseProjection_half.1
      diskPhysicalTransverseProjection_half.2 (diskSpectralFiberQuadraticBilinear parameter)

theorem diskSpectralMovingQuadraticCorrection_homological (parameter : PeriodicC1HolderHalf) :
    EulerNonuniqueness.General.quadraticCommutator diskRotatingDerivative
      (diskSpectralMovingQuadraticCorrection parameter) = diskSpectralProjectedQuadratic parameter := by
  have period : diskPhysicalGroup (4 * Real.pi) = ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
    simpa only [zero_add, diskPhysicalGroup_zero] using diskPhysicalGroup_period 0
  have identity : EulerNonuniqueness.General.quadraticCommutator diskRotatingDerivative
      (diskSpectralMovingQuadraticCorrection parameter) = diskSpectralProjectedQuadratic parameter -
      EulerNonuniqueness.General.quadraticResonance (Space := PeriodicC1HolderHalf)
        diskPhysicalGroup (4 * Real.pi) (diskSpectralProjectedQuadratic parameter) := by
    unfold diskSpectralMovingQuadraticCorrection
    with_reducible
      exact EulerNonuniqueness.General.quadratic_homological_identity
        (Space := PeriodicC1HolderHalf) diskPhysicalGroup diskRotatingDerivative
        (by positivity : 0 < 4 * Real.pi) diskPhysicalGroup_zero diskPhysicalGroup_add
        diskPhysicalGroup_generator period (diskSpectralProjectedQuadratic parameter)
  rw [diskSpectralProjectedQuadratic_resonance_zero, sub_zero] at identity
  exact identity

end

end EulerNonuniqueness.Paper
