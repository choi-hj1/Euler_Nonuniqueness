import EulerNonuniqueness.Section7.ReferenceOuterDisplacementFixedBound
import EulerNonuniqueness.Section4.ReferenceMaterialWitness
import EulerNonuniqueness.Section4.OuterDisplacementDecay
import EulerNonuniqueness.Section5.CascadeMaterialCenterGeometry
import EulerNonuniqueness.Section5.CascadeGeometricScaleSmallness

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem Scales.eventually_reference_observation_geometry (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {threshold referenceConstant : ℝ} (thresholdSmall : threshold ≤ 1 / 8)
    (referenceNonnegative : 0 ≤ referenceConstant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ {count : ℕ} {phase : Fin count → ℝ},
    ∀ witness : ReferenceMaterialCoarseWitness {scales with frequency := frequency} phase threshold referenceConstant,
    ∀ time ∈ Icc (0 : ℝ) 1,
    (∀ index patch position, position ∈ witness.trajectory.movingFamily.patchMotion.domain time index patch →
      ‖position - quadrupoleCenter witness.trajectory.movingFamily.patchMotion time index‖ ≤
        4 * ({scales with frequency := frequency} : Scales).length (index.val + 1)) ∧
    ∀ outer : Fin count, outer.val = 0 →
      ‖quadrupoleCenter witness.trajectory.movingFamily.patchMotion time outer - (scales.location 1 : ℂ)‖ ≤
        ({scales with frequency := frequency} : Scales).length 1 ∧
      ∀ patch position, position ∈ witness.trajectory.movingFamily.patchMotion.domain time outer patch →
        ‖position - (scales.location 1 : ℂ)‖ ≤ 5 * ({scales with frequency := frequency} : Scales).length 1 := by
  obtain ⟨constant, constantOne, outer⟩ := scales.exists_reference_outer_displacement_fixed_bound
    amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative
  have decay := (scales.outerDisplacementBound_tendsto_zero ratioBound alphaPositive).const_mul constant
  simp only [mul_zero] at decay
  filter_upwards [outer,
    decay.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num)]
    with frequency outer outerSmall mechanical geometry
  intro count phase witness time inside
  let changed : Scales := {scales with frequency := frequency}
  let motion := witness.trajectory.movingFamily.patchMotion
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, inside.2.trans (by norm_num)⟩
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have own (index : Fin count) (patch : Fin 4) (position : ℂ) (positionInside : position ∈ motion.domain time index patch) :
      ‖position - quadrupoleCenter motion time index‖ ≤ 4 * changed.length (index.val + 1) := by
    have domain := witness.trajectory.domain_subset_centroid_ball changed witness.radiusIdentity (fun _ => rfl) globalInside index patch positionInside
    rw [mem_closedBall, dist_eq_norm] at domain
    have center := (mechanical motion witness.evolution witness.coarse time referenceInside index).1.centroidsBounded patch
    have triangle := norm_sub_le_norm_sub_add_norm_sub position (patchCentroid motion time index patch) (quadrupoleCenter motion time index)
    have radius := (geometry (index.val + 1)).2.1
    linarith [changed.length_pos (index.val + 1)]
  refine ⟨own, ?_⟩
  intro index indexZero
  have center := outer motion witness.evolution witness.initial witness.coarse time referenceInside index indexZero
  have centerBound : ‖quadrupoleCenter motion time index - (changed.location 1 : ℂ)‖ ≤ changed.length 1 := by
    have normalized := center.trans outerSmall.le
    have multiplied := (div_le_iff₀ (changed.length_pos 1)).mp normalized
    simpa only [one_mul] using multiplied
  refine ⟨centerBound, ?_⟩
  intro patch position positionInside
  have near := own index patch position positionInside
  simp only [indexZero, zero_add] at near
  have triangle := norm_sub_le_norm_sub_add_norm_sub position (quadrupoleCenter motion time index) (changed.location 1 : ℂ)
  change ‖position - (changed.location 1 : ℂ)‖ ≤ 5 * changed.length 1
  linarith

end EulerNonuniqueness.Paper
