import EulerNonuniqueness.Section7.ReferenceObservationGeometry
import EulerNonuniqueness.Section5.CascadeStoppedMaterialGeometry
import EulerNonuniqueness.Section3.FinitePatchDomainSupport

noncomputable section

open Set Filter Metric Function
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem Scales.eventually_actual_finite_family_support (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {threshold referenceConstant : ℝ} (thresholdSmall : threshold ≤ 1 / 8)
    (referenceNonnegative : 0 ≤ referenceConstant) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {scaleRoot boundaryConstant shapeRadius factor monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ outer : Fin count, outer.val = 0 →
    (∀ time ∈ Icc 0 path.stop,
      support (patchVorticity {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion time) ⊆ closedBall 0 5) ∧
    ∀ time ∈ Icc (0 : ℝ) 1,
      support (patchVorticity {scales with frequency := frequency} prepared.referenceWitness.trajectory.movingFamily.patchMotion time) ⊆ closedBall 0 5 := by
  filter_upwards [scales.eventually_reference_observation_geometry amplitudePositive ratioBound alphaPositive thresholdSmall
      referenceNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num)]
    with frequency referenceGeometry geometry
  intro orbit sectionTime phase dipoleAngle scaleRoot boundaryConstant shapeRadius factor monitor count prepared path outer outerZero
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  constructor
  · intro time inside
    apply support_patchVorticity_subset_of_domain_subset
    intro index patch position positionInside
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
    have domain := prepared.trajectory.domain_subset_centroid_ball changed prepared.radiusIdentity (fun _ => rfl) globalInside index patch positionInside
    rw [mem_closedBall, dist_eq_norm] at domain
    have extent := (path.centroid_extent inside index patch).le
    have anchor := path.externalMonitors time inside (.anchor index)
    change ‖cascadeBlockCenter (prepared.trajectory.movingFamily.cascadeCenters time) index‖ - 3 < 0 at anchor
    rw [prepared.trajectory.cascadeBlockCenter_eq_quadrupoleCenter (fun _ => rfl) globalInside] at anchor
    have radius := (geometry (index.val + 1)).2.2.2
    have first := norm_sub_le_norm_sub_add_norm_sub position (patchCentroid motion time index patch) (quadrupoleCenter motion time index)
    have second := norm_add_le (position - quadrupoleCenter motion time index) (quadrupoleCenter motion time index)
    rw [sub_add_cancel] at second
    rw [mem_closedBall, dist_zero_right]
    linarith [changed.location_le_one (index.val + 1)]
  · intro time inside
    apply support_patchVorticity_subset_of_domain_subset
    intro index patch position positionInside
    have data := referenceGeometry prepared.referenceWitness time inside
    have own := data.1 index patch position positionInside
    have outerBound := (data.2 outer outerZero).1
    have outerNorm := norm_add_le (quadrupoleCenter reference time outer - (changed.location 1 : ℂ)) (changed.location 1 : ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (changed.location_pos 1)] at outerNorm
    have centerSeparation : ‖quadrupoleCenter reference time index - quadrupoleCenter reference time outer‖ ≤ 2 := by
      by_cases same : index = outer
      · simp [same]
      · have upper := (prepared.referenceWitness.coarse.2.2 time ⟨inside.1, inside.2.trans (by norm_num)⟩ index outer same).2
        have distance : |changed.location (index.val + 1) - changed.location (outer.val + 1)| ≤ 1 :=
          abs_le.mpr ⟨by linarith [changed.location_pos (index.val + 1), changed.location_le_one (outer.val + 1)],
            by linarith [changed.location_pos (outer.val + 1), changed.location_le_one (index.val + 1)]⟩
        linarith
    have small := (geometry (index.val + 1)).2.2.1
    have outerSmall := (geometry 1).2.2.1
    change ‖quadrupoleCenter reference time outer - (changed.location 1 : ℂ)‖ ≤ changed.length 1 at outerBound
    change ‖position - quadrupoleCenter reference time index‖ ≤ 4 * changed.length (index.val + 1) at own
    have first := norm_sub_le_norm_sub_add_norm_sub position (quadrupoleCenter reference time index) (quadrupoleCenter reference time outer)
    have second := norm_add_le (position - quadrupoleCenter reference time outer) (quadrupoleCenter reference time outer)
    rw [sub_add_cancel] at second
    rw [mem_closedBall, dist_zero_right]
    linarith [changed.location_le_one (index.val + 1), changed.location_le_one 1]

end EulerNonuniqueness.Paper
