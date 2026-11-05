import EulerNonuniqueness.Section5.CascadeMaterialCenterGeometry
import EulerNonuniqueness.Section5.CascadeForeignGapGeometry

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

theorem cascade_foreign_geometry_of_monitors {count : ℕ}
    {configuration : FiniteContourConfiguration (count * 4)}
    {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
    {initial : MovingContourState (count * 4)}
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (scales : Scales)
    (radii : ∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon)
    {factor : ℝ} (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (extent : ∀ label, cascadeExtentMonitor scales label (trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (lower : ∀ receiver source, cascadeAnchorLowerMonitor scales receiver source
      (trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (radiusSmall : ∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.location (index.val + 1) / 1000)
    (receiver source : Fin count) (different : source ≠ receiver) :
    0 < cascadeForeignDistance scales factor receiver source ∧
    8 * scales.radius (receiver.val + 1) ≤ cascadeForeignDistance scales factor receiver source ∧
    4 * scales.radius (source.val + 1) ≤ cascadeForeignDistance scales factor receiver source ∧
    (∀ target sourcePatch,
      cascadeForeignDistance scales factor receiver source ≤
        ‖patchCentroid trajectory.movingFamily.patchMotion time receiver target -
          patchCentroid trajectory.movingFamily.patchMotion time source sourcePatch‖) ∧
    (∀ target sourcePatch position, position ∈ trajectory.movingFamily.patchMotion.domain time source sourcePatch →
      cascadeForeignDistance scales factor receiver source ≤
        ‖patchCentroid trajectory.movingFamily.patchMotion time receiver target - position‖) ∧
    (∀ sourcePatch position, position ∈ trajectory.movingFamily.patchMotion.domain time source sourcePatch →
      cascadeForeignDistance scales factor receiver source ≤
        ‖quadrupoleCenter trajectory.movingFamily.patchMotion time receiver - position‖) := by
  let anchors := fun index => quadrupoleCenter trajectory.movingFamily.patchMotion time index
  have patchExtent (index : Fin count) (patch : Fin 4) :
      ‖patchCentroid trajectory.movingFamily.patchMotion time index patch - anchors index‖ ≤
        scales.location (index.val + 1) / 100 := by
    have estimate := sub_nonpos.mp (extent (index, patch))
    change ‖trajectory.movingFamily.cascadeCenters time (index, patch) -
      cascadeBlockCenter (trajectory.movingFamily.cascadeCenters time) index‖ ≤ _ at estimate
    rw [trajectory.cascadeCenters_eq_patchCentroid initialCircles inside,
      trajectory.cascadeBlockCenter_eq_quadrupoleCenter initialCircles inside] at estimate
    exact estimate
  have separation := lower receiver source
  rw [cascadeAnchorLowerMonitor, if_neg different.symm,
    trajectory.cascadeBlockCenter_eq_quadrupoleCenter initialCircles inside,
    trajectory.cascadeBlockCenter_eq_quadrupoleCenter initialCircles inside] at separation
  have geometry := cascadeForeignDistance_properties scales factorPositive factorSmall anchors receiver source
    different.symm (sub_nonpos.mp separation) radiusSmall
  have radiusNonnegative : 0 ≤ scales.radius (source.val + 1) := Real.sqrt_nonneg _
  have domainExtent (sourcePatch : Fin 4) (position : ℂ)
      (member : position ∈ trajectory.movingFamily.patchMotion.domain time source sourcePatch) :
      ‖position - anchors source‖ ≤ scales.location (source.val + 1) / 100 + 2 * scales.radius (source.val + 1) := by
    have bounded := trajectory.domain_subset_centroid_ball scales radii initialCircles inside source sourcePatch member
    rw [mem_closedBall, dist_eq_norm] at bounded
    have triangle := norm_sub_le_norm_sub_add_norm_sub position
      (patchCentroid trajectory.movingFamily.patchMotion time source sourcePatch) (anchors source)
    linarith [patchExtent source sourcePatch]
  refine ⟨geometry.1, geometry.2.1, geometry.2.2.1, ?_, ?_, ?_⟩
  · intro target sourcePatch
    exact geometry.2.2.2 _ _ (patchExtent receiver target)
      ((patchExtent source sourcePatch).trans (by linarith))
  · intro target sourcePatch position member
    exact geometry.2.2.2 _ _ (patchExtent receiver target) (domainExtent sourcePatch position member)
  · intro sourcePatch position member
    exact geometry.2.2.2 _ _ (by
      change ‖anchors receiver - anchors receiver‖ ≤ _
      rw [sub_self, norm_zero]
      exact div_nonneg (scales.location_pos _).le (by norm_num))
      (domainExtent sourcePatch position member)

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
