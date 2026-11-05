import EulerNonuniqueness.Section3.MovingContourCompactInitialMargin
import EulerNonuniqueness.Section3.MovingCentroidGaugeLocalUncut

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingCircleJointHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingCircleJointC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem FiniteContourConfiguration.exists_compact_joint_circle_material_trajectories
    {Parameter : Type*} [TopologicalSpace Parameter] [CompactSpace Parameter]
    {count : ℕ} (configuration : FiniteContourConfiguration count) (countPositive : 0 < count)
    (centers : Parameter → Fin count → ℂ) (centersContinuous : Continuous centers)
    (separation : ∀ parameter first second, first ≠ second →
      3 * (configuration.radius first + configuration.radius second) < ‖centers parameter first - centers parameter second‖) :
    ∃ centerBound shapeRadius gap margin horizon : ℝ,
      0 < margin ∧ 0 < horizon ∧ horizon < 1 ∧
      ∃ trajectories : (parameter : Parameter) →
        MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin 1 1
          (0, centers parameter, fun _ => standardCircleBanach),
        Continuous (fun point : Parameter × ℝ => (trajectories point.1).curve point.2) ∧
        ∀ parameter time, time ∈ Icc 0 horizon → margin ≤ infDist ((trajectories parameter).curve time)
          (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ := by
  obtain ⟨shapeRadius, shapePositive, _shapeSmall, families⟩ :=
    configuration.exists_joint_movingCentroidGaugeTrajectories_with_uniform_uncut_interval
  obtain ⟨centerBound, centerNonnegative, gap, gapPositive, margin, marginPositive, initialMargins⟩ :=
    configuration.exists_compact_circle_initial_margin countPositive centers centersContinuous separation shapePositive
  obtain ⟨horizon, horizonPositive, beforeFinal, trajectories, jointContinuous, safe⟩ :=
    families centerBound centerNonnegative gap gapPositive margin marginPositive 1 zero_lt_one 1 zero_lt_one
  let initial : Parameter → configuration.movingStateAdmissible centerBound shapeRadius gap :=
    fun parameter => ⟨(0, centers parameter, fun _ => standardCircleBanach), (initialMargins parameter).1⟩
  have initialContinuous : Continuous initial := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk (centersContinuous.prodMk continuous_const)
  refine ⟨centerBound, shapeRadius, gap, margin, horizon, marginPositive, horizonPositive, beforeFinal,
    (fun parameter => trajectories (initial parameter)), ?_, ?_⟩
  · exact jointContinuous.comp ((initialContinuous.comp continuous_fst).prodMk continuous_snd)
  · intro parameter time inside
    exact safe (initial parameter) (initialMargins parameter).2 time inside

end EulerNonuniqueness.Paper
