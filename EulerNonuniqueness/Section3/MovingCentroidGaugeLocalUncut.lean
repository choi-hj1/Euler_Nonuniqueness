import EulerNonuniqueness.Section3.MovingCentroidGaugeBoundedFamily
import EulerNonuniqueness.Section3.MovingCentroidGaugeEuler

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingGaugeLocalUncutHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingGaugeLocalUncutC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem FiniteContourConfiguration.exists_joint_movingCentroidGaugeTrajectories_with_uniform_uncut_interval {count : ℕ}
    (configuration : FiniteContourConfiguration count) :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
      ∀ centerBound ≥ 0, ∀ gap > 0, ∀ margin > 0, ∀ backwardHorizon > 0, ∀ forwardHorizon > 0,
      ∃ horizon > 0, horizon < forwardHorizon ∧
      ∃ trajectories : (initial : configuration.movingStateAdmissible centerBound shapeRadius gap) →
        MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial.val,
        Continuous (fun point : configuration.movingStateAdmissible centerBound shapeRadius gap × ℝ =>
          (trajectories point.1).curve point.2) ∧
        ∀ initial, 2 * margin ≤ infDist initial.val (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ →
          ∀ time ∈ Icc 0 horizon, margin ≤ infDist ((trajectories initial).curve time)
            (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, families⟩ :=
    configuration.exists_bounded_joint_movingCentroidGaugeTrajectories
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro centerBound centerNonnegative gap gapPositive margin marginPositive backwardHorizon backwardPositive forwardHorizon forwardPositive
  obtain ⟨bound, trajectories, jointContinuous, bounded⟩ :=
    families centerBound centerNonnegative gap gapPositive margin marginPositive backwardHorizon backwardPositive forwardHorizon forwardPositive
  let horizon : ℝ := min (forwardHorizon / 2) (margin / ((bound : ℝ) + 1))
  have horizonPositive : 0 < horizon := lt_min (by positivity) (by positivity)
  have beforeFinal : horizon < forwardHorizon := (min_le_left _ _).trans_lt (by linarith)
  have travelBudget : (bound : ℝ) * horizon ≤ margin := by
    have enlargedBudget : horizon * ((bound : ℝ) + 1) ≤ margin :=
      (le_div_iff₀ (by positivity : 0 < (bound : ℝ) + 1)).mp
        (show horizon ≤ margin / ((bound : ℝ) + 1) from min_le_right _ _)
    nlinarith
  refine ⟨horizon, horizonPositive, beforeFinal, trajectories, jointContinuous, ?_⟩
  intro initial initialMargin
  apply (trajectories initial).margin_of_velocity_bound bound.coe_nonneg
    (fun current _inside => bounded initial current) beforeFinal
  linarith

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : MovingContourState (count * 4)}

theorem finiteEuler_of_initial_margin_and_velocity_budget
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (scales : Scales)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (initialCircles : ∀ index, initial.2.2 index = standardCircleBanach)
    (marginPositive : 0 < margin) {horizon bound : ℝ}
    (horizonPositive : 0 < horizon) (beforeFinal : horizon < forwardHorizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ current ∈ Ioo (-backwardHorizon) forwardHorizon, ‖trajectory.velocity current‖ ≤ bound)
    (travelBudget : bound * horizon ≤ margin)
    (initialMargin : 2 * margin ≤ infDist initial (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) :
    FinitePatchEvolution scales trajectory.movingFamily.patchMotion horizon ∧
      IsEulerSolutionOn horizon (trajectory.movingFamily.vorticity 0) trajectory.movingFamily.vorticity := by
  have safe := trajectory.margin_of_velocity_bound boundNonnegative bounded beforeFinal
    (show margin + bound * horizon ≤ infDist initial
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ by linarith)
  exact ⟨trajectory.finitePatchEvolution_of_margin scales densityIdentity radiusIdentity initialCircles
      marginPositive horizonPositive.le beforeFinal safe,
    trajectory.isEulerSolutionOn_of_margin scales densityIdentity radiusIdentity initialCircles
      marginPositive horizonPositive beforeFinal amplitudePositive frequencyPositive ratioPositive safe⟩

end MovingCentroidGaugeTrajectory

end EulerNonuniqueness.Paper
