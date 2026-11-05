import EulerNonuniqueness.Section3.ContourDerivativeLipschitz
import EulerNonuniqueness.Section3.ContourBanachContinuity

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem contourVelocityBanach_value_component (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    (contourVelocityBanach data small).val.1 = boundedBanachContourVelocity data small := by
  apply BoundedContinuousFunction.ext
  intro label
  rfl

theorem contourVelocityBanach_tangent_component (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    (contourVelocityBanach data small).val.2 = contourVelocityDerivativeHolder data small := by
  apply PeriodicHolderHalf.ext_value
  intro label
  rfl

def contourVelocityBanachLipschitzConstant (radius : ℝ) : ℝ :=
  max ((1 + 2 * (radius + 2) / (2 / (3 * Real.pi) - radius)) / 2)
    (contourVelocityDerivativeLipschitzConstant radius)

theorem contourVelocityBanachLipschitzConstant_nonneg {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) : 0 ≤ contourVelocityBanachLipschitzConstant radius := by
  have chord_pos := sub_pos.mpr (radius_small.trans_le (min_le_right _ _))
  apply le_trans (b := (1 + 2 * (radius + 2) / (2 / (3 * Real.pi) - radius)) / 2)
  · positivity
  · exact le_max_left _ _

theorem contourVelocityBanach_parameter_norm_bound (first second : PeriodicC1HolderHalf) {radius : ℝ}
    (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius) (second_near : ‖second - standardCircleBanach‖ ≤ radius) :
    ‖contourVelocityBanach first (first_near.trans_lt radius_small) -
      contourVelocityBanach second (second_near.trans_lt radius_small)‖ ≤
      contourVelocityBanachLipschitzConstant radius * ‖first - second‖ := by
  change max
    ‖(contourVelocityBanach first (first_near.trans_lt radius_small)).val.1 -
      (contourVelocityBanach second (second_near.trans_lt radius_small)).val.1‖
    ‖(contourVelocityBanach first (first_near.trans_lt radius_small)).val.2 -
      (contourVelocityBanach second (second_near.trans_lt radius_small)).val.2‖ ≤ _
  rw [contourVelocityBanach_value_component, contourVelocityBanach_value_component,
    contourVelocityBanach_tangent_component, contourVelocityBanach_tangent_component]
  apply max_le
  · exact (boundedBanachContourVelocity_uniform_parameter_bound first second radius_nonneg radius_small first_near second_near).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · exact (contourVelocityDerivativeHolder_parameter_norm_bound first second radius_nonneg radius_small first_near second_near).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

def contourVelocityBanachBound (radius : ℝ) : ℝ := max ((radius + 3) / 2) (contourVelocityDerivativeConstant radius)

theorem contourVelocityBanach_uniform_norm_bound (data : PeriodicC1HolderHalf) {radius : ℝ}
    (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ radius) :
    ‖contourVelocityBanach data (nearby.trans_lt radius_small)‖ ≤ contourVelocityBanachBound radius := by
  apply (contourVelocityBanach_norm_bound data (nearby.trans_lt radius_small)).trans
  apply max_le_max
  · have bound := PeriodicC1HolderHalf.norm_le_radius_add_two data nearby
    linarith
  · exact contourVelocityDerivativeHolder_uniform_norm_bound data radius_nonneg radius_small nearby

def contourVelocityNearCircle (shape : NearCircleShape) : PeriodicC1HolderHalf :=
  contourVelocityBanach shape.val shape.property

set_option maxHeartbeats 1000000 in
theorem contourVelocityNearCircle_locallyLipschitz : LocallyLipschitz contourVelocityNearCircle := by
  intro shape
  let radius := (‖shape.val - standardCircleBanach‖ + min 1 (2 / (3 * Real.pi))) / 2
  have radius_larger : ‖shape.val - standardCircleBanach‖ < radius := by dsimp only [radius]; linarith [shape.property]
  have radius_small : radius < min 1 (2 / (3 * Real.pi)) := by dsimp only [radius]; linarith [shape.property]
  have radius_pos : 0 < radius := (norm_nonneg _).trans_lt radius_larger
  let constant : NNReal := ⟨contourVelocityBanachLipschitzConstant radius,
    contourVelocityBanachLipschitzConstant_nonneg radius_pos.le radius_small⟩
  let neighborhood := {other : NearCircleShape | ‖other.val - standardCircleBanach‖ < radius}
  have neighborhood_mem : neighborhood ∈ 𝓝 shape := by
    have norm_continuous : Continuous (fun other : NearCircleShape => ‖other.val - standardCircleBanach‖) := by
      have value_continuous : Continuous (fun other : NearCircleShape => other.val) := continuous_subtype_val
      convert value_continuous.dist
        (continuous_const : Continuous (fun _ : NearCircleShape => standardCircleBanach)) using 1
      funext other
      exact (dist_eq_norm other.val standardCircleBanach).symm
    have open_neighborhood : IsOpen neighborhood := isOpen_lt norm_continuous continuous_const
    exact open_neighborhood.mem_nhds radius_larger
  refine ⟨constant, neighborhood, neighborhood_mem, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro first first_mem second second_mem
  have bound := contourVelocityBanach_parameter_norm_bound first.val second.val radius_pos.le radius_small first_mem.le second_mem.le
  simpa only [contourVelocityNearCircle, dist_eq_norm, Subtype.dist_eq, constant, NNReal.coe_mk] using bound

theorem contourVelocityNearCircle_continuous : Continuous contourVelocityNearCircle :=
  contourVelocityNearCircle_locallyLipschitz.continuous

end

end EulerNonuniqueness.Paper
