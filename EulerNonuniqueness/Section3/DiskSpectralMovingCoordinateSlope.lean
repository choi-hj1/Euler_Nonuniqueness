import EulerNonuniqueness.Section3.DiskSpectralMovingCoordinateEquation
import EulerNonuniqueness.Section3.DiskSpectralMovingQuadraticLipschitz
import EulerNonuniqueness.General.MovingQuadraticInteraction

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter Set Metric
open scoped Topology

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectralMovingCoordinate_eventually_norm_slope_lt
    {admissible : Set PeriodicC1HolderHalf} {constant : NNReal}
    (openAdmissible : IsOpen admissible)
    (lipschitz : LipschitzOnWith constant diskSpectralMovingQuadraticCorrection admissible)
    {trajectory : ℝ → PeriodicC1HolderHalf} {time rate threshold : ℝ} {forcing : PeriodicC1HolderHalf}
    (equation : HasDerivAt trajectory (diskSpectralTubularEulerField (trajectory time) + forcing) time)
    (inside : diskRelabelNeutralCLM (trajectory time) ∈ admissible)
    (rateStrict : (constant : ℝ) *
      ‖diskRelabelNeutralCLM (diskSpectralTubularEulerField (trajectory time)) + diskRelabelNeutralCLM forcing‖ *
        ‖diskPhysicalTransverseProjection (trajectory time)‖ ^ 2 < rate)
    (strict : ‖diskPhysicalGroup (-time) (diskSpectralFrozenRemainder (trajectory time) forcing)‖ +
      diskPhysicalGroupBound * rate < threshold) :
    ∀ᶠ later in 𝓝[>] time,
      slope (fun current => ‖diskPhysicalGroup (-current)
        (EulerNonuniqueness.General.quadraticCoordinate
          (diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM (trajectory current))) 1
          (diskPhysicalTransverseProjection (trajectory current)))‖) time later < threshold := by
  have neutralDerivative := diskSpectralNeutral_trajectory_hasDerivAt equation
  have transverseDerivative := diskSpectralTransverse_trajectory_hasDerivAt equation
  have neutralContinuous : ContinuousAt (fun current => diskRelabelNeutralCLM (trajectory current)) time := by
    with_reducible
      exact HasDerivAt.continuousAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf) neutralDerivative
  have nearby : ∀ᶠ later in 𝓝 time, diskRelabelNeutralCLM (trajectory later) ∈ admissible := by
    with_reducible
      exact neutralContinuous.eventually_mem (openAdmissible.mem_nhds inside)
  have frozen := diskSpectralFrozenNeutralCoordinate_hasDerivAt equation
  with_reducible
    exact EulerNonuniqueness.General.eventually_moving_quadratic_interaction_norm_slope_lt
      (Parameter := PeriodicC1HolderHalf) (Space := PeriodicC1HolderHalf)
      diskPhysicalGroup diskRotatingDerivative diskPhysicalGroup_generator
      diskPhysicalGroupBound_nonnegative diskPhysicalGroup_norm_bound lipschitz
      neutralDerivative transverseDerivative.continuousAt inside nearby frozen rateStrict strict

end

end EulerNonuniqueness.Paper
