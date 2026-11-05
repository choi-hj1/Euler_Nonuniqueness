import EulerNonuniqueness.Section3.ContourPhaseParameter
import Mathlib.Topology.MetricSpace.Lipschitz

open Set Filter
open scoped Topology BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

abbrev NearCircleShape := {data : PeriodicC1HolderHalf //
  ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))}

noncomputable def contourVelocityToBounded (shape : NearCircleShape) : ℝ →ᵇ ℂ :=
  boundedBanachContourVelocity shape.val shape.property

set_option maxHeartbeats 1000000 in
theorem contourVelocityToBounded_locallyLipschitz : LocallyLipschitz contourVelocityToBounded := by
  intro shape
  let radius := (‖shape.val - standardCircleBanach‖ + min 1 (2 / (3 * Real.pi))) / 2
  have radius_larger : ‖shape.val - standardCircleBanach‖ < radius := by
    dsimp only [radius]
    linarith [shape.property]
  have radius_small : radius < min 1 (2 / (3 * Real.pi)) := by
    dsimp only [radius]
    linarith [shape.property]
  have radius_pos : 0 < radius := (norm_nonneg _).trans_lt radius_larger
  have denominator_pos : 0 < 2 / (3 * Real.pi) - radius :=
    sub_pos.mpr (radius_small.trans_le (min_le_right _ _))
  let constant : NNReal := ⟨(1 + 2 * (radius + 2) / (2 / (3 * Real.pi) - radius)) / 2, by positivity⟩
  let neighborhood := {other : NearCircleShape | ‖other.val - standardCircleBanach‖ < radius}
  have neighborhood_mem : neighborhood ∈ 𝓝 shape := by
    have norm_continuous : Continuous (fun other : NearCircleShape => ‖other.val - standardCircleBanach‖) := by
      have value_continuous : Continuous (fun other : NearCircleShape => other.val) := continuous_subtype_val
      convert value_continuous.dist
        (continuous_const : Continuous (fun _ : NearCircleShape => standardCircleBanach)) using 1
      funext other
      exact (dist_eq_norm other.val standardCircleBanach).symm
    have open_neighborhood : IsOpen neighborhood :=
      isOpen_lt norm_continuous continuous_const
    exact open_neighborhood.mem_nhds radius_larger
  refine ⟨constant, neighborhood, neighborhood_mem, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro first first_mem second second_mem
  have bound := boundedBanachContourVelocity_uniform_parameter_bound first.val second.val radius_pos.le
    radius_small first_mem.le second_mem.le
  simpa only [contourVelocityToBounded, dist_eq_norm, Subtype.dist_eq, constant, NNReal.coe_mk] using bound

theorem contourVelocityToBounded_continuous : Continuous contourVelocityToBounded :=
  contourVelocityToBounded_locallyLipschitz.continuous

end EulerNonuniqueness.Paper
