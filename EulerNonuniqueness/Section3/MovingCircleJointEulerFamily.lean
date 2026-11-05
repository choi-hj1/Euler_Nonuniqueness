import EulerNonuniqueness.Section3.MovingCircleJointMaterialFamily
import EulerNonuniqueness.Section3.MovingCentroidGaugeInitialBoundary

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingCircleJointEulerHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingCircleJointEulerC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem FiniteContourConfiguration.exists_compact_joint_circle_Euler_trajectories
    {Parameter : Type*} [TopologicalSpace Parameter] [CompactSpace Parameter]
    {count : ℕ} (countPositive : 0 < count) (configuration : FiniteContourConfiguration (count * 4))
    (scales : Scales) (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (centers : Parameter → Fin (count * 4) → ℂ) (centersContinuous : Continuous centers)
    (separation : ∀ parameter first second, first ≠ second →
      3 * (configuration.radius first + configuration.radius second) < ‖centers parameter first - centers parameter second‖) :
    ∃ centerBound shapeRadius gap margin horizon : ℝ,
      0 < margin ∧ 0 < horizon ∧ horizon < 1 ∧
      ∃ trajectories : (parameter : Parameter) →
        MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin 1 1
          (0, centers parameter, fun _ => standardCircleBanach),
        Continuous (fun point : Parameter × ℝ => (trajectories point.1).curve point.2) ∧
        (∀ parameter time, time ∈ Icc 0 horizon → margin ≤ infDist ((trajectories parameter).curve time)
          (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) ∧
        ∀ parameter,
          FinitePatchEvolution scales (trajectories parameter).movingFamily.patchMotion horizon ∧
          IsEulerSolutionOn horizon ((trajectories parameter).movingFamily.vorticity 0)
            (trajectories parameter).movingFamily.vorticity ∧
          ∀ index patch,
            (trajectories parameter).movingFamily.patchMotion.domain 0 index patch =
              Metric.ball (centers parameter (finProdFinEquiv (index, patch))) (scales.radius (index.val + 1)) ∧
            ∀ label, (trajectories parameter).movingFamily.patchMotion.boundary 0 index patch label =
              centers parameter (finProdFinEquiv (index, patch)) +
                (scales.radius (index.val + 1) : ℂ) * Complex.exp (Complex.I * (label : ℂ)) := by
  obtain ⟨centerBound, shapeRadius, gap, margin, horizon, marginPositive, horizonPositive, beforeFinal,
      trajectories, jointContinuous, safe⟩ := configuration.exists_compact_joint_circle_material_trajectories
        (Nat.mul_pos countPositive (by norm_num)) centers centersContinuous separation
  refine ⟨centerBound, shapeRadius, gap, margin, horizon, marginPositive, horizonPositive, beforeFinal,
    trajectories, jointContinuous, safe, ?_⟩
  intro parameter
  have initialCircles : ∀ index : Fin (count * 4),
      ((0 : ℝ), centers parameter, fun _ : Fin (count * 4) => standardCircleBanach).2.2 index = standardCircleBanach := fun _ => rfl
  refine ⟨(trajectories parameter).finitePatchEvolution_of_margin scales densityIdentity radiusIdentity initialCircles
      marginPositive horizonPositive.le beforeFinal (safe parameter),
    (trajectories parameter).isEulerSolutionOn_of_margin scales densityIdentity radiusIdentity initialCircles
      marginPositive horizonPositive beforeFinal amplitudePositive frequencyPositive ratioPositive (safe parameter), ?_⟩
  intro index patch
  constructor
  · change ((trajectories parameter).movingPatch (finProdFinEquiv (index, patch))).domain 0 = _
    rw [(trajectories parameter).movingPatch_domain_initial_circle initialCircles, radiusIdentity]
  · intro label
    change ((trajectories parameter).movingPatch (finProdFinEquiv (index, patch))).boundary 0 label = _
    rw [(trajectories parameter).movingPatch_boundary_initial_circle rfl initialCircles, radiusIdentity]

end EulerNonuniqueness.Paper
