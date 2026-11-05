import EulerNonuniqueness.Section8.RegularizedAdvectionVelocity

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal Topology

namespace EulerNonuniqueness.RegularizedFlowOn

theorem support_vorticity_subset_at_time {source : Vorticity} {integrable : Integrable source}
    {scale horizon : ℝ} {positive : 0 < scale}
    (flow : RegularizedFlowOn source integrable scale positive horizon)
    (nonnegative : 0 ≤ horizon) (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    {radius : ℝ} (supported : support source ⊆ Metric.closedBall 0 radius)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    support (flow.vorticity time) ⊆ Metric.closedBall 0 (radius + regularizedSourceSpeed source * time) := by
  change support (injectionAdvection (flow.particleMap time) source) ⊆ _
  rw [support_injectionAdvection (flow.injective_particleMap inside)]
  rintro position ⟨label, labelSupported, rfl⟩
  have labelBound : ‖label‖ ≤ radius := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using supported labelSupported
  change ‖label + flow.displacement time label - 0‖ ≤ _
  rw [sub_zero]
  exact (norm_add_le _ _).trans (add_le_add labelBound
    (((flow.displacement time).norm_coe_le_norm label).trans
      (flow.norm_displacement_le_sourceSpeed nonnegative membership inside)))

end EulerNonuniqueness.RegularizedFlowOn
