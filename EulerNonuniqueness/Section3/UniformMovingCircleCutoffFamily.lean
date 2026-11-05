import EulerNonuniqueness.Section3.UniformMovingCentroidGaugeFamily
import EulerNonuniqueness.Section3.MovingContourCompactInitialMargin

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance uniformCircleFamilyHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance uniformCircleFamilyC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem exists_uniform_compact_circle_cutoff_families :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
      ∀ {Parameter : Type*} [TopologicalSpace Parameter] [CompactSpace Parameter],
      ∀ count : ℕ, 0 < count → ∀ configuration : FiniteContourConfiguration count,
      ∀ centers : Parameter → Fin count → ℂ, Continuous centers →
      (∀ parameter first second, first ≠ second →
        3 * (configuration.radius first + configuration.radius second) < ‖centers parameter first - centers parameter second‖) →
      ∀ backwardHorizon > 0, ∀ forwardHorizon > 0,
      ∃ centerBound gap margin : ℝ, 0 ≤ centerBound ∧ 0 < gap ∧ 0 < margin ∧
        ∃ trajectories : (parameter : Parameter) →
          MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon
            (0, centers parameter, fun _ => standardCircleBanach),
          Continuous (fun point : Parameter × ℝ => (trajectories point.1).curve point.2) ∧
          ∀ parameter, 2 * margin ≤ infDist
            ((0 : ℝ), centers parameter, fun _ : Fin count => standardCircleBanach)
            (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, families⟩ :=
    exists_uniform_moving_centroid_gauge_trajectory_families
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro Parameter parameterTopology parameterCompact count countPositive configuration centers centersContinuous separated
    backwardHorizon backwardPositive forwardHorizon forwardPositive
  obtain ⟨centerBound, centerNonnegative, gap, gapPositive, margin, marginPositive, initialMargins⟩ :=
    configuration.exists_compact_circle_initial_margin countPositive centers centersContinuous separated shapePositive
  obtain ⟨trajectories, jointContinuous⟩ := families count configuration centerBound centerNonnegative gap gapPositive
    margin marginPositive backwardHorizon backwardPositive forwardHorizon forwardPositive
  let initial : Parameter → configuration.movingStateAdmissible centerBound shapeRadius gap :=
    fun parameter => ⟨(0, centers parameter, fun _ => standardCircleBanach), (initialMargins parameter).1⟩
  have initialContinuous : Continuous initial := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk (centersContinuous.prodMk continuous_const)
  refine ⟨centerBound, gap, margin, centerNonnegative, gapPositive, marginPositive,
    (fun parameter => trajectories (initial parameter)), ?_, ?_⟩
  · exact jointContinuous.comp ((initialContinuous.comp continuous_fst).prodMk continuous_snd)
  · intro parameter
    exact (initialMargins parameter).2

end EulerNonuniqueness.Paper
