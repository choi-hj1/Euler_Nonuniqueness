import EulerNonuniqueness.Section3.MovingContourInitialMargin
import EulerNonuniqueness.Section3.MovingCentroidGaugeLocalUncut
import EulerNonuniqueness.Section3.SeparatedDiskPatchExistence

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingCircleMaterialHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingCircleMaterialC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem FiniteContourConfiguration.exists_movingCircle_material_trajectory {count : ℕ}
    (configuration : FiniteContourConfiguration count) (countPositive : 0 < count) :
    ∃ centerBound shapeRadius gap margin horizon : ℝ,
      0 < margin ∧ 0 < horizon ∧ horizon < 1 ∧
      ∃ trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin 1 1
        configuration.movingCircleInitialState,
        ∀ time ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve time)
          (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ := by
  obtain ⟨shapeRadius, shapePositive, _shapeSmall, families⟩ :=
    configuration.exists_joint_movingCentroidGaugeTrajectories_with_uniform_uncut_interval
  obtain ⟨centerBound, centerNonnegative, gap, gapPositive, margin, marginPositive, initialInside, initialMargin⟩ :=
    configuration.exists_movingCircleInitialState_margin countPositive shapePositive
  obtain ⟨horizon, horizonPositive, beforeFinal, trajectories, _jointContinuous, safe⟩ :=
    families centerBound centerNonnegative gap gapPositive margin marginPositive
      1 zero_lt_one 1 zero_lt_one
  let initial : configuration.movingStateAdmissible centerBound shapeRadius gap :=
    ⟨configuration.movingCircleInitialState, initialInside⟩
  exact ⟨centerBound, shapeRadius, gap, margin, horizon, marginPositive, horizonPositive, beforeFinal,
    trajectories initial, safe initial initialMargin⟩

theorem exists_moving_material_finiteEuler_from_separated_disks {count : ℕ} (countPositive : 0 < count)
    (scales : Scales) (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (centers : Fin count × Fin 4 → ℂ)
    (separation : ∀ first second : Fin count × Fin 4, first ≠ second →
      3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) < ‖centers first - centers second‖) :
    ∃ horizon > 0, ∃ family : FiniteMovingPatchFamily (count * 4),
      FinitePatchEvolution scales family.patchMotion horizon ∧
      IsEulerSolutionOn horizon (family.vorticity 0) family.vorticity ∧
      ∀ index patch, family.patchMotion.domain 0 index patch =
        Metric.ball (centers (index, patch)) (scales.radius (index.val + 1)) := by
  let configuration := separatedDiskConfiguration scales amplitudePositive frequencyPositive ratioPositive centers separation
  obtain ⟨centerBound, shapeRadius, gap, margin, horizon, marginPositive, horizonPositive, beforeFinal, trajectory, safe⟩ :=
    configuration.exists_movingCircle_material_trajectory (Nat.mul_pos countPositive (by norm_num))
  have densityIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 := by
    intro index patch
    simp only [configuration, separatedDiskConfiguration, Equiv.symm_apply_apply]
  have radiusIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) =
      scales.radius (index.val + 1) := by
    intro index patch
    simp only [configuration, separatedDiskConfiguration, Equiv.symm_apply_apply]
  have initialCircles : ∀ index, configuration.movingCircleInitialState.2.2 index = standardCircleBanach := fun _ => rfl
  refine ⟨horizon, horizonPositive, trajectory.movingFamily,
    trajectory.finitePatchEvolution_of_margin scales densityIdentity radiusIdentity initialCircles
      marginPositive horizonPositive.le beforeFinal safe,
    trajectory.isEulerSolutionOn_of_margin scales densityIdentity radiusIdentity initialCircles
      marginPositive horizonPositive beforeFinal amplitudePositive frequencyPositive ratioPositive safe, ?_⟩
  intro index patch
  change (trajectory.movingPatch (finProdFinEquiv (index, patch))).domain 0 = _
  rw [trajectory.movingPatch_domain_initial_circle initialCircles]
  simp only [FiniteContourConfiguration.movingCircleInitialState, configuration,
    separatedDiskConfiguration, Equiv.symm_apply_apply]

end EulerNonuniqueness.Paper
