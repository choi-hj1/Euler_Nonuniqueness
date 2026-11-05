import EulerNonuniqueness.Section3.DiskSpectralMovingQuadraticEquation
import EulerNonuniqueness.General.MovingQuadraticForcingSplit

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete
  chartedThirdBilinearGroup chartedThirdBilinearSpace chartedThirdBilinearComplete

local instance movingQuadraticSplitC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskSpectralMovingQuadraticSelfVelocity (state : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskSpectralFrozenQuadraticVelocity state 0 -
    fderiv ℝ diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM state)
      (diskRelabelNeutralCLM (diskSpectralTubularEulerField state))
      (diskPhysicalTransverseProjection state) (diskPhysicalTransverseProjection state)

def diskSpectralMovingQuadraticForcing (state forcing : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  let value := diskPhysicalTransverseProjection state
  diskPhysicalTransverseProjection forcing -
    (diskSpectralMovingQuadraticCorrection state (diskPhysicalTransverseProjection forcing) value +
      diskSpectralMovingQuadraticCorrection state value (diskPhysicalTransverseProjection forcing)) -
    fderiv ℝ diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM state)
      (diskRelabelNeutralCLM forcing) value value

theorem diskSpectralMovingQuadraticVelocity_forcing_split (state forcing : PeriodicC1HolderHalf) :
    diskSpectralFrozenQuadraticVelocity state forcing -
      fderiv ℝ diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM state)
        (diskRelabelNeutralCLM (diskSpectralTubularEulerField state + forcing))
        (diskPhysicalTransverseProjection state) (diskPhysicalTransverseProjection state) =
      diskSpectralMovingQuadraticSelfVelocity state + diskSpectralMovingQuadraticForcing state forcing := by
  let differential : PeriodicC1HolderHalf →L[ℝ]
      EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
    fderiv ℝ diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM state)
  unfold diskSpectralMovingQuadraticSelfVelocity diskSpectralMovingQuadraticForcing
    diskSpectralFrozenQuadraticVelocity
  with_reducible_and_instances
    exact EulerNonuniqueness.General.movingProjectedQuadraticVelocity_forcing_split
      diskPhysicalTransverseProjection diskRelabelNeutralCLM diskRotatingDerivative
      diskSpectralProjectedQuadratic diskSpectralMovingQuadraticCorrection diskSpectralTubularEulerField
      differential state forcing

theorem diskSpectralMovingQuadraticCoordinate_eventually_split_hasDerivAt :
    ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf),
    ∀ (trajectory : ℝ → PeriodicC1HolderHalf) (time : ℝ) (forcing : PeriodicC1HolderHalf),
    trajectory time = state →
    HasDerivAt trajectory (diskSpectralTubularEulerField state + forcing) time →
    HasDerivAt (fun current =>
      let value := diskPhysicalTransverseProjection (trajectory current)
      value - diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM (trajectory current)) value value)
      (diskSpectralMovingQuadraticSelfVelocity state + diskSpectralMovingQuadraticForcing state forcing) time := by
  filter_upwards [diskSpectralMovingQuadraticCoordinate_eventually_hasDerivAt] with state actual
  intro trajectory time forcing stateEquation equation
  exact (actual trajectory time forcing stateEquation equation).congr_deriv
    (diskSpectralMovingQuadraticVelocity_forcing_split state forcing)

end

end EulerNonuniqueness.Paper
