import EulerNonuniqueness.Section4.ReferenceUniformCutoffFamily

noncomputable section

open Filter Set Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance referenceShootingFamilyHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance referenceShootingFamilyC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem Scales.exists_uniform_eventually_reference_shooting_families
    (scales : Scales) (amplitudePositive : 0 < scales.amplitude)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
      ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ count : ℕ, 0 < count → ∀ phase : Fin count → ℝ,
      ∀ shootingRadius > 0, shootingRadius ≤ 1 / 2 →
      ∃ configuration : FiniteContourConfiguration (count * 4),
        (∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
          patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4) ∧
        (∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) =
          changed.radius (index.val + 1)) ∧
        ∃ centerBound gap margin : ℝ, 0 ≤ centerBound ∧ 0 < gap ∧ 0 < margin ∧
          ∃ trajectories : (parameter : closedBall (0 : Fin count → ℝ) shootingRadius) →
            MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin 1 3
              (0, (fun label => initialDiskCenter changed ((finProdFinEquiv.symm label).1.val + 1)
                (phase (finProdFinEquiv.symm label).1) (parameter.val (finProdFinEquiv.symm label).1)
                (finProdFinEquiv.symm label).2), fun _ => standardCircleBanach),
            Continuous (fun point : closedBall (0 : Fin count → ℝ) shootingRadius × ℝ =>
              (trajectories point.1).curve point.2) ∧
            (∀ parameter : closedBall (0 : Fin count → ℝ) shootingRadius, 2 * margin ≤ infDist
              ((0 : ℝ), (fun label : Fin (count * 4) => initialDiskCenter changed ((finProdFinEquiv.symm label).1.val + 1)
                (phase (finProdFinEquiv.symm label).1) (parameter.val (finProdFinEquiv.symm label).1)
                (finProdFinEquiv.symm label).2), fun _ => standardCircleBanach)
              (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) ∧
            (∀ parameter time, time ∈ Ico 0 3 →
              (trajectories parameter).curve time ∈ movingContinuousContourSubmodule (count * 4)) ∧
            (∀ parameter index, movingReferenceShapeCoordinates changed ((trajectories parameter).curve 0) index =
              (parameter.val index, 0)) ∧
            ∀ parameter, ReferenceInitialDisks changed (trajectories parameter).movingFamily.patchMotion
              phase parameter.val (1 / 2) := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, families⟩ := exists_uniform_compact_reference_cutoff_families
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_initialDiskCenters_separated amplitudePositive ratioBound alphaPositive]
    with frequency frequencyPositive separation
  dsimp only
  intro count countPositive phase shootingRadius shootingPositive shootingSmall
  let changed : Scales := {scales with frequency := frequency}
  let Parameter := closedBall (0 : Fin count → ℝ) shootingRadius
  letI : CompactSpace Parameter := isCompact_iff_compactSpace.mp
    (isCompact_closedBall (0 : Fin count → ℝ) shootingRadius)
  letI : Nonempty Parameter := ⟨⟨0, by simpa only [Parameter, mem_closedBall, dist_self] using shootingPositive.le⟩⟩
  have unstableSmall (parameter : Parameter) (index : Fin count) : |parameter.val index| ≤ 1 / 2 := by
    have normBound : ‖parameter.val‖ ≤ shootingRadius := by
      simpa only [Parameter, mem_closedBall, dist_zero_right] using parameter.property
    have coordinateBound : |parameter.val index| ≤ ‖parameter.val‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm parameter.val index
    exact coordinateBound.trans (normBound.trans shootingSmall)
  exact families count countPositive changed amplitudePositive frequencyPositive
    (show 0 < changed.ratio by dsimp only [changed]; linarith)
    phase (fun parameter : Parameter => parameter.val) continuous_subtype_val unstableSmall
    (fun parameter => separation count phase parameter.val (unstableSmall parameter))
    1 (by norm_num) 3 (by norm_num)

end EulerNonuniqueness.Paper
