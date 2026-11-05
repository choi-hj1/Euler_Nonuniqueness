import EulerNonuniqueness.Section3.FixedRelabelForcingJets
import EulerNonuniqueness.Section3.DiskChartedEulerField
import EulerNonuniqueness.General.LinearRelabelResidual

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance rotatingRelabelResidualC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

theorem diskEulerRotatingField_fixedRelabel (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ <
      min 1 (2 / (3 * Real.pi))) :
    diskEulerRotatingField (fixedRelabelEquivalence angular angularSmall data) =
      fixedRelabelEquivalence angular angularSmall (diskEulerRotatingField data) := by
  unfold diskEulerRotatingField
  rw [extendedContourVelocity_fixedRelabelEquivalence angular angularSmall data small composedSmall, map_sub]
  congr 1
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

theorem differentiableAt_diskEulerRotatingField (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    DifferentiableAt ℝ diskEulerRotatingField data := by
  exact (differentiableAt_extendedContourVelocity data small).sub
    (c1ProductCLM (c1Constant (Complex.I / 2))).differentiableAt

def centeredForcingHomologicalResidual (degree : ℕ) (coefficient : ℂ)
    (correction : PeriodicC1HolderHalf → PeriodicC1HolderHalf) : PeriodicC1HolderHalf → PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.forcingJetResidual diskEulerRotatingField (centeredAntiholomorphicForcing degree)
    correction (c1ProductCLM (c1Constant coefficient))

theorem centeredForcingHomologicalResidual_fixedRelabel (degree : ℕ) (coefficient : ℂ)
    (angular : PeriodicC1HolderHalf) (angularSmall : ‖angular‖ < 1 / 2)
    (correction : PeriodicC1HolderHalf → PeriodicC1HolderHalf) (data : PeriodicC1HolderHalf)
    (regular : DifferentiableAt ℝ correction data)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ <
      min 1 (2 / (3 * Real.pi))) :
    centeredForcingHomologicalResidual degree coefficient
      (EulerNonuniqueness.General.linearRelabelCorrection (fixedRelabelEquivalence angular angularSmall) correction)
      (fixedRelabelEquivalence angular angularSmall data) =
      fixedRelabelEquivalence angular angularSmall (centeredForcingHomologicalResidual degree coefficient correction data) := by
  have firstNeighborhood : ∀ᶠ current in 𝓝 data,
      ‖current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) :=
    (isOpen_lt ((continuous_id.sub continuous_const).norm) continuous_const).mem_nhds small
  have secondNeighborhood : ∀ᶠ current in 𝓝 data,
      ‖fixedRelabelEquivalence angular angularSmall current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) :=
    (isOpen_lt (((fixedRelabelEquivalence angular angularSmall).continuous.sub continuous_const).norm)
      continuous_const).mem_nhds composedSmall
  apply EulerNonuniqueness.General.forcingJetResidual_linearRelabel
    diskEulerRotatingField (centeredAntiholomorphicForcing degree) correction
    (c1ProductCLM (c1Constant coefficient)) (fixedRelabelEquivalence angular angularSmall) data
    (differentiableAt_diskEulerRotatingField data small)
    (differentiableAt_diskEulerRotatingField (fixedRelabelEquivalence angular angularSmall data) composedSmall) regular
  · filter_upwards [firstNeighborhood, secondNeighborhood] with current firstNear secondNear
    exact diskEulerRotatingField_fixedRelabel angular angularSmall current firstNear secondNear
  · exact centeredAntiholomorphicForcing_fixedRelabel degree angular angularSmall data
  · intro direction
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rfl

end EulerNonuniqueness.Paper
