import EulerNonuniqueness.Section3.UniformContinuousCircleCutoffFamily
import EulerNonuniqueness.Section3.MovingCentroidGaugeInitialBoundary
import EulerNonuniqueness.Section4.ReferenceInitialJointEuler
import EulerNonuniqueness.Section4.MovingReferenceShootingCoordinates

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance referenceUniformCutoffHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance referenceUniformCutoffC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem exists_uniform_compact_reference_cutoff_families :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
      ∀ {Parameter : Type*} [TopologicalSpace Parameter] [CompactSpace Parameter] [Nonempty Parameter],
      ∀ count : ℕ, 0 < count → ∀ scales : Scales,
      0 < scales.amplitude → 0 < scales.frequency → 0 < scales.ratio →
      ∀ (phase : Fin count → ℝ) (unstable : Parameter → Fin count → ℝ),
      Continuous unstable → (∀ parameter index, |unstable parameter index| ≤ 1 / 2) →
      (∀ (parameter : Parameter) (first second : Fin count × Fin 4), first ≠ second →
        3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) <
          ‖initialDiskCenter scales (first.1.val + 1) (phase first.1) (unstable parameter first.1) first.2 -
            initialDiskCenter scales (second.1.val + 1) (phase second.1) (unstable parameter second.1) second.2‖) →
      ∀ backwardHorizon > 0, ∀ forwardHorizon > 0,
      ∃ configuration : FiniteContourConfiguration (count * 4),
        (∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
          patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) ∧
        (∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) =
          scales.radius (index.val + 1)) ∧
        ∃ centerBound gap margin : ℝ, 0 ≤ centerBound ∧ 0 < gap ∧ 0 < margin ∧
          ∃ trajectories : (parameter : Parameter) →
            MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon
              (0, (fun label => initialDiskCenter scales ((finProdFinEquiv.symm label).1.val + 1)
                (phase (finProdFinEquiv.symm label).1) (unstable parameter (finProdFinEquiv.symm label).1)
                (finProdFinEquiv.symm label).2), fun _ => standardCircleBanach),
            Continuous (fun point : Parameter × ℝ => (trajectories point.1).curve point.2) ∧
            (∀ parameter, 2 * margin ≤ infDist
              ((0 : ℝ), (fun label : Fin (count * 4) => initialDiskCenter scales ((finProdFinEquiv.symm label).1.val + 1)
                (phase (finProdFinEquiv.symm label).1) (unstable parameter (finProdFinEquiv.symm label).1)
                (finProdFinEquiv.symm label).2), fun _ => standardCircleBanach)
              (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) ∧
            (∀ parameter time, time ∈ Ico 0 forwardHorizon →
              (trajectories parameter).curve time ∈ movingContinuousContourSubmodule (count * 4)) ∧
            (∀ parameter index, movingReferenceShapeCoordinates scales ((trajectories parameter).curve 0) index =
              (unstable parameter index, 0)) ∧
            ∀ parameter, ReferenceInitialDisks scales (trajectories parameter).movingFamily.patchMotion
              phase (unstable parameter) (1 / 2) := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, families⟩ :=
    exists_uniform_compact_continuous_circle_cutoff_families
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro Parameter parameterTopology parameterCompact parameterNonempty count countPositive scales
    amplitudePositive frequencyPositive ratioPositive phase unstable unstableContinuous unstableSmall separation
    backwardHorizon backwardPositive forwardHorizon forwardPositive
  classical
  let centers : Parameter → Fin (count * 4) → ℂ := fun parameter label =>
    initialDiskCenter scales ((finProdFinEquiv.symm label).1.val + 1)
      (phase (finProdFinEquiv.symm label).1) (unstable parameter (finProdFinEquiv.symm label).1)
      (finProdFinEquiv.symm label).2
  let base : Parameter := Classical.choice inferInstance
  let configuration := separatedDiskConfiguration scales amplitudePositive frequencyPositive ratioPositive
    (fun label => initialDiskCenter scales (label.1.val + 1) (phase label.1) (unstable base label.1) label.2)
    (separation base)
  have densityIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 := by
    intro index patch
    simp only [configuration, separatedDiskConfiguration, Equiv.symm_apply_apply]
  have radiusIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) =
      scales.radius (index.val + 1) := by
    intro index patch
    simp only [configuration, separatedDiskConfiguration, Equiv.symm_apply_apply]
  have centersContinuous : Continuous centers := by
    apply continuous_pi
    intro label
    exact initialDiskCenter_continuous_of_unstable_bound scales _ _ _
      (fun parameter => unstable parameter (finProdFinEquiv.symm label).1)
      ((continuous_apply (finProdFinEquiv.symm label).1).comp unstableContinuous)
      (fun parameter => (unstableSmall parameter _).trans (by norm_num))
  have centersSeparated : ∀ parameter first second, first ≠ second →
      3 * (configuration.radius first + configuration.radius second) < ‖centers parameter first - centers parameter second‖ := by
    intro parameter first second different
    exact separation parameter (finProdFinEquiv.symm first) (finProdFinEquiv.symm second)
      (fun identity => different (finProdFinEquiv.symm.injective identity))
  obtain ⟨centerBound, gap, margin, centerNonnegative, gapPositive, marginPositive,
      trajectories, jointContinuous, initialMargin, continuousVectors⟩ :=
    families (count * 4) (Nat.mul_pos countPositive (by norm_num)) configuration centers centersContinuous centersSeparated
      backwardHorizon backwardPositive forwardHorizon forwardPositive
  refine ⟨configuration, densityIdentity, radiusIdentity, centerBound, gap, margin, centerNonnegative, gapPositive,
    marginPositive, trajectories, jointContinuous, initialMargin, continuousVectors, ?_, ?_⟩
  · intro parameter index
    rw [(trajectories parameter).initial_identity]
    exact movingReferenceShapeCoordinates_initial scales phase (unstable parameter) (unstableSmall parameter) index
  · intro parameter index
    have initialCircles : ∀ label : Fin (count * 4),
        ((0 : ℝ), centers parameter, fun _ : Fin (count * 4) => standardCircleBanach).2.2 label = standardCircleBanach :=
      fun _ => rfl
    refine ⟨unstableSmall parameter index, fun patch => ⟨?_, ?_⟩⟩
    · change ((trajectories parameter).movingPatch (finProdFinEquiv (index, patch))).domain 0 = _
      rw [(trajectories parameter).movingPatch_domain_initial_circle initialCircles, radiusIdentity]
      simp only [centers, Equiv.symm_apply_apply]
    · intro label
      change ((trajectories parameter).movingPatch (finProdFinEquiv (index, patch))).boundary 0 label = _
      rw [(trajectories parameter).movingPatch_boundary_initial_circle rfl initialCircles, radiusIdentity]
      simp only [centers, Equiv.symm_apply_apply]

end EulerNonuniqueness.Paper
