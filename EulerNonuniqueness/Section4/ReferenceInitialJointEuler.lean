import EulerNonuniqueness.Section4.InitialReferenceDiskSeparation
import EulerNonuniqueness.Section4.ReferenceInitialCenterContinuity
import EulerNonuniqueness.Section3.MovingCircleJointEulerFamily
import EulerNonuniqueness.Section3.SeparatedDiskPatchExistence

noncomputable section

open Filter Set Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance referenceJointEulerHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance referenceJointEulerC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem exists_compact_initial_reference_joint_Euler
    {Parameter : Type*} [TopologicalSpace Parameter] [CompactSpace Parameter] [Nonempty Parameter]
    {count : ℕ} (countPositive : 0 < count)
    (scales : Scales) (amplitudePositive : 0 < scales.amplitude)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (phase : Fin count → ℝ) (unstable : Parameter → Fin count → ℝ)
    (unstableContinuous : Continuous unstable) (unstableSmall : ∀ parameter index, |unstable parameter index| ≤ 1 / 2)
    (separation : ∀ (parameter : Parameter) (first second : Fin count × Fin 4), first ≠ second →
      3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) <
        ‖initialDiskCenter scales (first.1.val + 1) (phase first.1) (unstable parameter first.1) first.2 -
          initialDiskCenter scales (second.1.val + 1) (phase second.1) (unstable parameter second.1) second.2‖) :
    ∃ configuration : FiniteContourConfiguration (count * 4),
      (∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) ∧
      (∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) ∧
      ∃ centerBound shapeRadius gap margin horizon : ℝ,
        0 < margin ∧ 0 < horizon ∧ horizon < 1 ∧
        ∃ trajectories : (parameter : Parameter) →
          MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin 1 1
            (0, (fun label => initialDiskCenter scales ((finProdFinEquiv.symm label).1.val + 1)
              (phase (finProdFinEquiv.symm label).1) (unstable parameter (finProdFinEquiv.symm label).1)
              (finProdFinEquiv.symm label).2), fun _ => standardCircleBanach),
          Continuous (fun point : Parameter × ℝ => (trajectories point.1).curve point.2) ∧
          (∀ parameter time, time ∈ Icc 0 horizon → margin ≤ infDist ((trajectories parameter).curve time)
            (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) ∧
          ∀ parameter,
            FinitePatchEvolution scales (trajectories parameter).movingFamily.patchMotion horizon ∧
            IsEulerSolutionOn horizon ((trajectories parameter).movingFamily.vorticity 0)
              (trajectories parameter).movingFamily.vorticity ∧
            ReferenceInitialDisks scales (trajectories parameter).movingFamily.patchMotion phase (unstable parameter) (1 / 2) := by
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
  obtain ⟨centerBound, shapeRadius, gap, margin, horizon, marginPositive, horizonPositive, beforeFinal,
      trajectories, jointContinuous, safe, evolution⟩ :=
    configuration.exists_compact_joint_circle_Euler_trajectories countPositive scales amplitudePositive
      frequencyPositive ratioPositive densityIdentity radiusIdentity centers centersContinuous centersSeparated
  refine ⟨configuration, densityIdentity, radiusIdentity, centerBound, shapeRadius, gap, margin, horizon,
    marginPositive, horizonPositive, beforeFinal, trajectories, jointContinuous, safe, ?_⟩
  intro parameter
  refine ⟨(evolution parameter).1, (evolution parameter).2.1, ?_⟩
  intro index
  refine ⟨unstableSmall parameter index, ?_⟩
  intro patch
  simpa only [centers, Equiv.symm_apply_apply] using (evolution parameter).2.2 index patch

end EulerNonuniqueness.Paper
