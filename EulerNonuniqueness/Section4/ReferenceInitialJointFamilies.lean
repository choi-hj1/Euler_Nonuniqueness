import EulerNonuniqueness.Section4.ReferenceInitialJointEuler
import EulerNonuniqueness.Section3.MovingCentroidGaugeJointCentroids

noncomputable section

open Filter Set
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance referenceJointFamiliesHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance referenceJointFamiliesC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem Scales.eventually_compact_reference_initial_Euler_families
    {Parameter : Type*} [TopologicalSpace Parameter] [CompactSpace Parameter] [Nonempty Parameter]
    (scales : Scales) (amplitudePositive : 0 < scales.amplitude)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, 0 < count →
      ∀ (phase : Fin count → ℝ) (unstable : Parameter → Fin count → ℝ), Continuous unstable →
        (∀ parameter index, |unstable parameter index| ≤ 1 / 2) →
        ∃ horizon : ℝ, 0 < horizon ∧ horizon < 1 ∧
          ∃ families : Parameter → FiniteMovingPatchFamily (count * 4),
            (∀ index patch, ContinuousOn (fun point : Parameter × ℝ =>
              patchCentroid (families point.1).patchMotion point.2 index patch)
              {point | point.2 ∈ Icc 0 horizon}) ∧
            ∀ parameter,
              FinitePatchEvolution {scales with frequency := frequency} (families parameter).patchMotion horizon ∧
              IsEulerSolutionOn horizon ((families parameter).vorticity 0) (families parameter).vorticity ∧
              ReferenceInitialDisks {scales with frequency := frequency} (families parameter).patchMotion
                phase (unstable parameter) (1 / 2) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_initialDiskCenters_separated amplitudePositive ratioBound alphaPositive]
    with frequency frequencyPositive separated count countPositive phase unstable unstableContinuous unstableSmall
  let changed : Scales := {scales with frequency := frequency}
  obtain ⟨configuration, _densityIdentity, _radiusIdentity, centerBound, shapeRadius, gap, margin, horizon,
      _marginPositive, horizonPositive, beforeFinal, trajectories, jointContinuous, _safe, evolution⟩ :=
    exists_compact_initial_reference_joint_Euler countPositive changed amplitudePositive frequencyPositive
      (show 0 < changed.ratio by dsimp only [changed]; linarith) phase unstable unstableContinuous unstableSmall
      (fun parameter => separated count phase (unstable parameter) (unstableSmall parameter))
  refine ⟨horizon, horizonPositive, beforeFinal, (fun parameter => (trajectories parameter).movingFamily), ?_, evolution⟩
  intro index patch
  have initialCircles : ∀ parameter label,
      ((0 : ℝ), (fun label : Fin (count * 4) => initialDiskCenter changed ((finProdFinEquiv.symm label).1.val + 1)
        (phase (finProdFinEquiv.symm label).1) (unstable parameter (finProdFinEquiv.symm label).1)
        (finProdFinEquiv.symm label).2), fun _ : Fin (count * 4) => standardCircleBanach).2.2 label = standardCircleBanach :=
    fun _ _ => rfl
  apply (MovingCentroidGaugeTrajectory.joint_patchCentroid_continuousOn_interior trajectories jointContinuous initialCircles index patch).mono
  intro point inside
  exact ⟨(by norm_num : -(1 : ℝ) < 0).trans_le inside.1, inside.2.trans_lt beforeFinal⟩

end EulerNonuniqueness.Paper
