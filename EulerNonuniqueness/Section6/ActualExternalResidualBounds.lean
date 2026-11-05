import EulerNonuniqueness.Section6.ActualExternalCentroidDynamics

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

theorem subfamilyExternalReceiverResidual_bound {count : ℕ}
    {configuration : FiniteContourConfiguration count} (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (receiver : Fin count) (densityNonzero : configuration.density receiver ≠ 0)
    (receiverCenter : ℂ) {deformation : ℝ} (deformationNonnegative : 0 ≤ deformation)
    (deformationSmall : deformation ≤ 1 / 16)
    (receiverLower : Metric.ball receiverCenter (configuration.radius receiver * (1 - deformation)) ⊆ flow.domain time receiver)
    (receiverUpper : flow.domain time receiver ⊆ Metric.ball receiverCenter (configuration.radius receiver * (1 + deformation)))
    (sourceBounded : ∀ source ∈ Finset.univ \ selected,
      flow.domain time source ⊆ Metric.closedBall (flow.centroid time source) (2 * configuration.radius source))
    (separated : ∀ source ∈ Finset.univ \ selected,
      8 * configuration.radius receiver ≤ ‖flow.centroid time receiver - flow.centroid time source‖ ∧
      4 * configuration.radius source ≤ ‖flow.centroid time receiver - flow.centroid time source‖) :
    ‖flow.subfamilyExternalReceiverResidual selected time receiver‖ ≤
      (1024 * configuration.radius receiver ^ 2 * deformation / Real.pi) *
        ∑ source ∈ Finset.univ \ selected,
          |configuration.density source * (Real.pi * configuration.radius source ^ 2)| /
            ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3 := by
  unfold subfamilyExternalReceiverResidual
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ source ∈ Finset.univ \ selected,
        1024 * |configuration.density source * (Real.pi * configuration.radius source ^ 2)| *
          configuration.radius receiver ^ 2 * deformation /
          (Real.pi * ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3) := by
      apply Finset.sum_le_sum
      intro source member
      exact flow.component_actual_receiver_averaging_bound_of_trapping inside receiver source densityNonzero
        receiverCenter deformationNonnegative deformationSmall receiverLower receiverUpper (sourceBounded source member)
        (separated source member).1 (separated source member).2
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro source _
      ring

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
