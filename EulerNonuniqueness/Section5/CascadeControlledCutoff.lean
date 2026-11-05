import EulerNonuniqueness.Section5.CascadeCutoffSlack
import EulerNonuniqueness.Section3.UniformMovingContinuousGaugeFamily
import EulerNonuniqueness.Section3.MovingContourInitialMargin
import EulerNonuniqueness.Section3.SeparatedDiskPatchExistence

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

local instance cascadeControlledHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance cascadeControlledC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem exists_uniform_controlled_cascade_cutoff_paths :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
    ∀ scales : Scales, 0 < scales.amplitude → 0 < scales.frequency → 0 < scales.ratio →
    ∀ count : ℕ, 0 < count → ∀ factor : ℝ, 0 < factor →
    ∀ centers : Fin count × Fin 4 → ℂ, (∀ label, ‖centers label‖ ≤ 3) →
    (∀ first second, first ≠ second →
      3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) +
        4 * cascadePairCutoffSlack scales factor first second ≤ ‖centers first - centers second‖) →
    ∃ configuration : FiniteContourConfiguration (count * 4),
      (∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) ∧
      (∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) ∧
    ∃ gap > (0 : ℝ), ∃ margin > (0 : ℝ), margin ≤ shapeRadius / 8 ∧ margin ≤ 1 / 8 ∧
      (∀ first second : Fin count × Fin 4, gap + 4 * margin ≤ 4 * cascadePairCutoffSlack scales factor first second) ∧
    ∃ trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin 1 3
      (0, (fun label => centers (finProdFinEquiv.symm label)), fun _ => standardCircleBanach),
      2 * margin ≤ infDist (trajectory.curve 0) (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ ∧
      (∀ time ∈ Ico (0 : ℝ) 3, trajectory.curve time ∈ movingContinuousContourSubmodule (count * 4)) := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, families⟩ := exists_uniform_moving_continuous_gauge_trajectory_families
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro scales amplitudePositive frequencyPositive ratioPositive count countPositive factor factorPositive centers centerBound pairBound
  obtain ⟨gap, gapPositive, margin, marginPositive, marginShape, marginUnit, marginSlack⟩ :=
    exists_cascade_cutoff_parameters (count := count) scales factorPositive shapePositive
  have separated (first second : Fin count × Fin 4) (different : first ≠ second) :
      3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) < ‖centers first - centers second‖ := by
    linarith [pairBound first second different, cascadePairCutoffSlack_pos scales factorPositive first second]
  let configuration := separatedDiskConfiguration scales amplitudePositive frequencyPositive ratioPositive centers separated
  have densityIdentity : ∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 := by
    intro index patch
    simp only [configuration, separatedDiskConfiguration, Equiv.symm_apply_apply]
  have radiusIdentity : ∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1) := by
    intro index patch
    simp only [configuration, separatedDiskConfiguration, Equiv.symm_apply_apply]
  let initial : MovingContourState (count * 4) :=
    (0, (fun label => centers (finProdFinEquiv.symm label)), fun _ => standardCircleBanach)
  have initialMargin : 2 * margin ≤ infDist initial (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ := by
    apply configuration.movingStateAdmissible_infDist_lower_bound (by omega) (by norm_num)
    · intro label
      change ‖centers (finProdFinEquiv.symm label)‖ + 2 * margin ≤ 4
      linarith [centerBound (finProdFinEquiv.symm label)]
    · intro label
      change ‖standardCircleBanach - standardCircleBanach‖ + 2 * margin ≤ shapeRadius
      rw [sub_self (standardCircleBanach : PeriodicC1HolderHalf), norm_zero (E := PeriodicC1HolderHalf), zero_add]
      linarith
    · intro first second different
      have bound := pairBound (finProdFinEquiv.symm first) (finProdFinEquiv.symm second)
        (fun equality => different (finProdFinEquiv.symm.injective equality))
      have slack := marginSlack (finProdFinEquiv.symm first) (finProdFinEquiv.symm second)
      change 3 * (configuration.radius first + configuration.radius second) + gap + 2 * (2 * margin) ≤
        ‖centers (finProdFinEquiv.symm first) - centers (finProdFinEquiv.symm second)‖
      dsimp only [configuration, separatedDiskConfiguration] at bound ⊢
      linarith
  have initialInside : initial ∈ configuration.movingStateAdmissible 4 shapeRadius gap := by
    apply Classical.byContradiction
    intro outside
    have zero : infDist initial (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ = 0 := infDist_zero_of_mem outside
    rw [zero] at initialMargin
    linarith
  obtain ⟨trajectories, _, preserves⟩ := families (count * 4) configuration 4 (by norm_num)
    gap gapPositive margin marginPositive 1 (by norm_num) 3 (by norm_num)
  let trajectory := trajectories ⟨initial, initialInside⟩
  refine ⟨configuration, densityIdentity, radiusIdentity, gap, gapPositive, margin, marginPositive,
    marginShape, marginUnit, marginSlack, trajectory, ?_, ?_⟩
  · rw [trajectory.initial_identity]
    exact initialMargin
  · exact preserves ⟨initial, initialInside⟩ (movingCircleInitial_mem_continuousSubmodule 0 _) 

end EulerNonuniqueness.Paper
