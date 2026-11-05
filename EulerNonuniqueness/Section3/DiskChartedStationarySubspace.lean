import EulerNonuniqueness.Section3.DiskChartedSpectralTrivialization
import EulerNonuniqueness.General.StationaryLinearSubspaceDerivative
import EulerNonuniqueness.General.CubicSpectralFixedKernel

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

theorem diskRelabelNeutralCLM_idempotent (increment : PeriodicC1HolderHalf) :
    diskRelabelNeutralCLM (diskRelabelNeutralCLM increment) = diskRelabelNeutralCLM increment := by
  have zeroReal (label : ℝ) : star ((0 : PeriodicC1HolderHalf).val.1 label) =
      (0 : PeriodicC1HolderHalf).val.1 label := by change star (0 : ℂ) = 0; simp
  have hilbertZero : periodicHilbertC1 (0 : PeriodicC1HolderHalf) = 0 := by
    exact map_zero periodicHilbertC1CLM
  have neutralIdentity : diskNeutralCLM (diskMaterialPerturbation 0 (diskNeutralCLM increment)) =
      diskNeutralCLM increment := by
    rw [diskNeutralCLM_apply,
      diskAngularCLM_materialPerturbation _ _ zeroReal (diskNeutralCLM_real increment),
      diskRadialPart_materialPerturbation _ _ zeroReal (diskNeutralCLM_real increment), hilbertZero]
    exact add_zero _
  rw [diskRelabelNeutralCLM_apply, diskRelabelNeutralCLM_apply, neutralIdentity]

theorem diskRotatingDerivative_relabel_neutral_zero (increment : PeriodicC1HolderHalf) :
    diskRotatingDerivative (diskRelabelNeutralCLM increment) = 0 := by
  rw [diskRelabelNeutralCLM_apply, ← diskRelabel_tangent_eq_material]
  exact diskRotatingDerivative_relabel_tangent_zero _ (diskNeutralCLM_real increment)

theorem diskChartedNeutralOperator_eventually_annihilates_relabel :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      (diskChartedNeutralOperator increment).comp diskRelabelNeutralCLM = 0 := by
  unfold diskChartedNeutralOperator
  with_reducible
    exact EulerNonuniqueness.General.eventually_fderiv_annihilates_stationary_subspace
      (Space := PeriodicC1HolderHalf) diskChartedEulerField diskRelabelNeutralCLM
      (diskChartedEulerField_eventually_twice_differentiable.mono fun _ actual => actual.1)
      diskChartedEulerField_eventually_neutral_stationary

theorem diskChartedSpectralCoordinates_eventually_fixes_relabel :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf), ∀ direction : PeriodicC1HolderHalf,
      diskChartedSpectralCoordinates increment (diskRelabelNeutralCLM direction) = diskRelabelNeutralCLM direction := by
  filter_upwards [diskChartedNeutralOperator_eventually_annihilates_relabel] with increment actual direction
  have kernel : diskChartedNeutralOperator increment (diskRelabelNeutralCLM direction) = 0 :=
    congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => linear direction) actual
  have referenceKernel := diskRotatingDerivative_relabel_neutral_zero direction
  unfold diskChartedSpectralCoordinates
  with_reducible
    exact EulerNonuniqueness.General.cubicSpectralIntertwiner_fixed_of_common_kernel
      (Space := PeriodicC1HolderHalf) (diskChartedNeutralOperator increment) diskRotatingDerivative
      (diskRelabelNeutralCLM direction) kernel referenceKernel

theorem diskChartedSpectralCoordinates_neutral_parameter (increment : PeriodicC1HolderHalf) :
    diskChartedSpectralCoordinates (diskRelabelNeutralCLM increment) = diskChartedSpectralCoordinates increment := by
  unfold diskChartedSpectralCoordinates diskChartedNeutralOperator
  rw [diskRelabelNeutralCLM_idempotent]

end

end EulerNonuniqueness.Paper
