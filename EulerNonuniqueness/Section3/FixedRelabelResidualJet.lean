import EulerNonuniqueness.Section3.FixedRelabelCorrectionBounds
import EulerNonuniqueness.General.LinearConjugateJet

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance relabelResidualJetC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

theorem centeredForcingHomologicalResidual_fixedRelabel_hasFDerivAt (degree : ℕ) (coefficient : ℂ)
    (angular : PeriodicC1HolderHalf) (angularSmall : ‖angular‖ < 1 / 2)
    (correction : PeriodicC1HolderHalf → PeriodicC1HolderHalf) (data : PeriodicC1HolderHalf)
    (derivative : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
    (regular : ∀ᶠ current in 𝓝 data, DifferentiableAt ℝ correction current)
    (jet : HasFDerivAt (centeredForcingHomologicalResidual degree coefficient correction) derivative data)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ <
      min 1 (2 / (3 * Real.pi))) :
    HasFDerivAt
      (centeredForcingHomologicalResidual degree coefficient
        (EulerNonuniqueness.General.linearRelabelCorrection (fixedRelabelEquivalence angular angularSmall) correction))
      ((fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap.comp
        (derivative.comp (fixedRelabelEquivalence angular angularSmall).symm.toContinuousLinearMap))
      (fixedRelabelEquivalence angular angularSmall data) := by
  apply EulerNonuniqueness.General.HasFDerivAt.linear_conjugate jet
    (fixedRelabelEquivalence angular angularSmall)
  have firstNeighborhood : ∀ᶠ current in 𝓝 data,
      ‖current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) :=
    (isOpen_lt ((continuous_id.sub continuous_const).norm) continuous_const).mem_nhds small
  have secondNeighborhood : ∀ᶠ current in 𝓝 data,
      ‖fixedRelabelEquivalence angular angularSmall current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) :=
    (isOpen_lt (((fixedRelabelEquivalence angular angularSmall).continuous.sub continuous_const).norm)
      continuous_const).mem_nhds composedSmall
  filter_upwards [regular, firstNeighborhood, secondNeighborhood] with current currentRegular firstNear secondNear
  exact centeredForcingHomologicalResidual_fixedRelabel degree coefficient angular angularSmall
    correction current currentRegular firstNear secondNear

end EulerNonuniqueness.Paper
