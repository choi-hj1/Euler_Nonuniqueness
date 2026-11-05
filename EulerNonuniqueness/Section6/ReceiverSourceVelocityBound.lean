import EulerNonuniqueness.Section6.PatchExternalCentroidLaw

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem norm_biotSavart_le_of_support_separation {vorticity : Vorticity}
    (integrable : Integrable vorticity) (position : ℂ) {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ source ∈ Function.support vorticity, distance ≤ ‖position - source‖) :
    ‖biotSavart vorticity position‖ ≤ (∫ source, |vorticity source|) / (2 * Real.pi * distance) := by
  have estimate := norm_integral_le_of_norm_le
    (f := fun source => vorticity source • biotSavartKernel (position - source))
    (integrable.norm.div_const (2 * Real.pi * distance)) (Filter.Eventually.of_forall fun source => by
      by_cases zero : vorticity source = 0
      · simp [zero]
      rw [norm_smul, Real.norm_eq_abs, norm_biotSavartKernel]
      have kernelBound : 1 / (2 * Real.pi * ‖position - source‖) ≤ 1 / (2 * Real.pi * distance) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_left (separated source (Function.mem_support.mpr zero)) (by positivity))
      exact (mul_le_mul_of_nonneg_left kernelBound (abs_nonneg _)).trans_eq (by ring))
  simpa only [biotSavart, integral_div, Real.norm_eq_abs] using estimate

theorem norm_receiver_biotSavart_le {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center position : ℂ) {radius : ℝ}
    (supported : Function.support vorticity ⊆ Metric.closedBall center radius)
    (outside : 2 * radius ≤ ‖position - center‖) (nonzero : position ≠ center) :
    ‖biotSavart vorticity position‖ ≤ (∫ source, |vorticity source|) / (Real.pi * ‖position - center‖) := by
  have normPositive : 0 < ‖position - center‖ := norm_pos_iff.mpr (sub_ne_zero.mpr nonzero)
  have positive : 0 < ‖position - center‖ / 2 := by positivity
  have estimate := norm_biotSavart_le_of_support_separation integrable position positive (by
    intro source member
    have localBound : ‖source - center‖ ≤ radius := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using supported member
    have triangle := norm_add_le (position - source) (source - center)
    rw [sub_add_sub_cancel] at triangle
    linarith)
  convert estimate using 1 <;> congr 1 <;> ring

end EulerNonuniqueness.Section6
