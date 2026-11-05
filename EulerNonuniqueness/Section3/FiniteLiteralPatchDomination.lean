import EulerNonuniqueness.Section3.FiniteLiteralPatchMeasurability
import EulerNonuniqueness.Section3.FiniteLiteralPatchMoments
import EulerNonuniqueness.Section8.MeasurableKernelConvolution

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem domain_subset_ball (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (index : Fin count) :
    flow.domain time index ⊆ Metric.ball (configuration.center index) (2 * configuration.radius index) := by
  rintro position ⟨normalized, member, rfl⟩
  have bound := nearCircleInterior_subset_ball (flow.shape time index)
    ((flow.nearby time index).trans_le (min_le_left _ _)) member
  have small := (flow.nearby time index).trans_le (min_le_left _ _)
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (configuration.radius_pos index)]
  have normalized_bound : ‖normalized‖ < 1 + ‖flow.shape time index - standardCircleBanach‖ := by
    simpa only [Metric.mem_ball, dist_zero_right] using bound
  have norm_bound : ‖normalized‖ < 2 := by linarith
  nlinarith [configuration.radius_pos index]

def dominator (flow : FiniteLiteralPatchFlow configuration) (position : ℂ) : ℝ :=
  ∑ index, |configuration.density index| *
    (Metric.ball (configuration.center index) (2 * configuration.radius index)).indicator (fun _ => (1 : ℝ)) position

theorem dominator_memLp (flow : FiniteLiteralPatchFlow configuration) (exponent : ℝ≥0∞) :
    MemLp flow.dominator exponent volume := by
  apply memLp_finset_sum
  intro index _
  exact (memLp_indicator_const exponent measurableSet_ball (1 : ℝ)
    (Or.inr (measure_ball_lt_top.ne))).const_mul _

theorem norm_vorticity_le_dominator (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (position : ℂ) :
    ‖flow.vorticity time position‖ ≤ flow.dominator position := by
  dsimp only [vorticity, FiniteContourConfiguration.literalVorticity, dominator]
  apply (norm_sum_le Finset.univ _).trans
  apply Finset.sum_le_sum
  intro index _
  by_cases member : position ∈ flow.domain time index
  · have ball_member := flow.domain_subset_ball time index member
    simp only [domain] at member
    rw [indicator_of_mem member, indicator_of_mem ball_member, mul_one, mul_one, Real.norm_eq_abs]
  · have domain_nonmember : position ∉ configuration.literalDomain (flow.shape time)
        (fun index => (flow.nearby time index).trans_le (min_le_left _ _)) index := member
    rw [indicator_of_not_mem domain_nonmember, mul_zero, norm_zero]
    exact mul_nonneg (abs_nonneg _) ((indicator_nonneg fun _ _ => zero_le_one) position)

theorem measurable_biotSavart_joint (flow : FiniteLiteralPatchFlow configuration) :
    Measurable (fun pair : ℝ × ℂ => biotSavart (flow.vorticity pair.1) pair.2) :=
  measurable_biotSavart_of_measurable_vorticity flow.measurable_vorticity_joint

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
