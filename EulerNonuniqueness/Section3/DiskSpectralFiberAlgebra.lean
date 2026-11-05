import EulerNonuniqueness.Section3.DiskSpectralTubularEquation
import EulerNonuniqueness.General.OperatorProjectionFiber

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskNeutralCLM_rotatingDerivative_zero (increment : PeriodicC1HolderHalf) :
    diskNeutralCLM (diskRotatingDerivative increment) = 0 := by
  have coordinates := diskPhysicalCoordinates_generator increment
  have radial := congrArg Prod.fst coordinates
  have angular := congrArg Prod.snd coordinates
  rw [diskLinearGenerator_apply] at radial angular
  change diskRadialPart (diskRotatingDerivative increment) =
    (-1 / 2 : ℝ) • periodicHilbertC1 (diskRadialPart increment) at radial
  change diskAngularCLM (diskRotatingDerivative increment) =
    (-1 / 2 : ℝ) • periodicMeanZeroPartCCLM (diskRadialPart increment) at angular
  rw [diskNeutralCLM_apply]
  change diskAngularCLM (diskRotatingDerivative increment) +
    periodicHilbertC1 (diskRadialPart (diskRotatingDerivative increment)) = 0
  rw [radial, angular, periodicHilbertC1_smul, periodicHilbertC1_sq]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (-1 / 2 : ℝ) • (periodicMeanZeroPartCCLM (diskRadialPart increment)).val.1 label +
    (-1 / 2 : ℝ) • (-(periodicMeanZeroPartCCLM (diskRadialPart increment)).val.1 label) = (0 : ℂ)
  simp only [Complex.real_smul]
  push_cast
  ring

theorem diskRelabelNeutralCLM_rotatingDerivative_zero (increment : PeriodicC1HolderHalf) :
    diskRelabelNeutralCLM (diskRotatingDerivative increment) = 0 := by
  rw [diskRelabelNeutralCLM_apply, diskNeutralCLM_rotatingDerivative_zero]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change standardCircle label * ((0 : ℂ) + Complex.I * 0) = 0
  ring

theorem diskSpectralTubularChart_fiber_identity (increment : PeriodicC1HolderHalf) :
    diskSpectralTubularChart increment = diskRelabelNeutralCLM increment +
      diskChartedSpectralCoordinates increment (increment - diskRelabelNeutralCLM increment) := by
  unfold diskSpectralTubularChart EulerNonuniqueness.General.spectralTubularChart
  rfl

theorem diskChartedSpectralCoordinates_eventually_derivative_annihilates_rotation :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf), ∀ direction : PeriodicC1HolderHalf,
      fderiv ℝ diskChartedSpectralCoordinates (diskRelabelNeutralCLM increment)
        (diskRotatingDerivative direction) = 0 := by
  have neutralLimit : Tendsto diskRelabelNeutralCLM (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 0) := by
    simpa only [map_zero] using diskRelabelNeutralCLM.continuous.tendsto (0 : PeriodicC1HolderHalf)
  filter_upwards [neutralLimit.eventually diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.1] with increment regular direction
  have idempotent := diskRelabelNeutralCLM_idempotent increment
  have kernel := diskRelabelNeutralCLM_rotatingDerivative_zero direction
  with_reducible
    exact EulerNonuniqueness.General.fderiv_operator_zero_on_projection_kernel
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskChartedSpectralCoordinates
      (diskRelabelNeutralCLM increment) (diskRotatingDerivative direction)
      diskChartedSpectralCoordinates_neutral_parameter idempotent kernel regular

end

end EulerNonuniqueness.Paper
