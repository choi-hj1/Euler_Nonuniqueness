import EulerNonuniqueness.Section3.DiskSpectralScaledBounds
import EulerNonuniqueness.Section3.DiskPhysicalScaledGroup
import EulerNonuniqueness.Section3.DiskSpectralMovingCoordinateSlope

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

theorem diskSpectralMovingQuadraticCorrection_exists_lipschitz_ball :
    ∃ radius > 0, ∃ constant : NNReal,
      LipschitzOnWith constant diskSpectralMovingQuadraticCorrection (ball (0 : PeriodicC1HolderHalf) radius) := by
  obtain ⟨constant, neighborhood, nearby, lipschitz⟩ := diskSpectralMovingQuadraticCorrection_lipschitzNear
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp nearby
  exact ⟨radius, positive, constant, lipschitz.mono contained⟩

theorem diskSpectralScaledCoordinate_eventually_norm_slope_lt
    (frequency : ℝ) {admissible : Set PeriodicC1HolderHalf} {constant : NNReal}
    (openAdmissible : IsOpen admissible)
    (lipschitz : LipschitzOnWith constant diskSpectralMovingQuadraticCorrection admissible)
    {trajectory : ℝ → PeriodicC1HolderHalf} {time rate threshold : ℝ} {forcing : PeriodicC1HolderHalf}
    (equation : HasDerivAt trajectory (frequency • diskSpectralTubularEulerField (trajectory time) + forcing) time)
    (inside : diskRelabelNeutralCLM (trajectory time) ∈ admissible)
    (rateStrict : (constant : ℝ) *
      ‖frequency • diskRelabelNeutralCLM (diskSpectralTubularEulerField (trajectory time)) + diskRelabelNeutralCLM forcing‖ *
        ‖diskPhysicalTransverseProjection (trajectory time)‖ ^ 2 < rate)
    (strict : ‖diskPhysicalScaledGroup frequency (-time)
      (diskSpectralScaledFrozenRemainder frequency (trajectory time) forcing)‖ +
        diskPhysicalGroupBound * rate < threshold) :
    ∀ᶠ later in 𝓝[>] time,
      slope (fun current => ‖diskPhysicalScaledGroup frequency (-current)
        (EulerNonuniqueness.General.quadraticCoordinate
          (diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM (trajectory current))) 1
          (diskPhysicalTransverseProjection (trajectory current)))‖) time later < threshold := by
  have neutralDerivative := diskSpectralScaledNeutral_trajectory_hasDerivAt frequency equation
  have transverseDerivative := EulerNonuniqueness.General.linear_projected_field_hasDerivAt
    diskPhysicalTransverseProjection (fun value => frequency • diskSpectralTubularEulerField value) equation
  have neutralContinuous : ContinuousAt (fun current => diskRelabelNeutralCLM (trajectory current)) time := by
    with_reducible
      exact HasDerivAt.continuousAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf) neutralDerivative
  have transverseContinuous : ContinuousAt (fun current => diskPhysicalTransverseProjection (trajectory current)) time := by
    with_reducible
      exact HasDerivAt.continuousAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf) transverseDerivative
  have nearby : ∀ᶠ later in 𝓝 time, diskRelabelNeutralCLM (trajectory later) ∈ admissible := by
    with_reducible
      exact neutralContinuous.eventually_mem (openAdmissible.mem_nhds inside)
  have frozen := diskSpectralScaledFrozenCoordinate_hasDerivAt frequency equation
  with_reducible
    exact EulerNonuniqueness.General.eventually_moving_quadratic_interaction_norm_slope_lt
      (Parameter := PeriodicC1HolderHalf) (Space := PeriodicC1HolderHalf)
      (diskPhysicalScaledGroup frequency) (frequency • diskRotatingDerivative)
      (diskPhysicalScaledGroup_generator frequency) diskPhysicalGroupBound_nonnegative
      (diskPhysicalScaledGroup_norm_bound frequency) lipschitz
      neutralDerivative transverseContinuous inside nearby frozen rateStrict strict

end

end EulerNonuniqueness.Paper
