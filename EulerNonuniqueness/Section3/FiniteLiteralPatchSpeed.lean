import EulerNonuniqueness.Section3.FiniteLiteralPatchDomination

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

noncomputable section

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

def speedBound (flow : FiniteLiteralPatchFlow configuration) : ℝ :=
  (eLpNorm flow.dominator (ENNReal.ofReal (4 : ℝ)) volume).toReal *
    (eLpNorm ((Metric.ball (0 : ℂ) 1).indicator biotSavartKernel)
      (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
      (∫ position, flow.dominator position) * (1 / (2 * Real.pi))

theorem dominator_integrable (flow : FiniteLiteralPatchFlow configuration) : Integrable flow.dominator :=
  memLp_one_iff_integrable.mp (flow.dominator_memLp 1)

theorem dominator_nonneg (flow : FiniteLiteralPatchFlow configuration) (position : ℂ) :
    0 ≤ flow.dominator position :=
  (norm_nonneg (flow.vorticity 0 position)).trans (flow.norm_vorticity_le_dominator 0 position)

theorem speedBound_nonneg (flow : FiniteLiteralPatchFlow configuration) : 0 ≤ flow.speedBound := by
  exact add_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (mul_nonneg (integral_nonneg flow.dominator_nonneg) (by positivity))

theorem norm_biotSavart_le_speedBound (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (position : ℂ) :
    ‖biotSavart (flow.vorticity time) position‖ ≤ flow.speedBound := by
  have four_bound : (eLpNorm (flow.vorticity time) (ENNReal.ofReal (4 : ℝ)) volume).toReal ≤
      (eLpNorm flow.dominator (ENNReal.ofReal (4 : ℝ)) volume).toReal :=
    ENNReal.toReal_mono (flow.dominator_memLp _).2.ne
      (eLpNorm_mono_real (flow.norm_vorticity_le_dominator time))
  have one_bound : (∫ source, ‖flow.vorticity time source‖) ≤ ∫ source, flow.dominator source :=
    integral_mono (flow.vorticity_integrable time).norm flow.dominator_integrable
      (flow.norm_vorticity_le_dominator time)
  exact (norm_biotSavart_le_L1_L4 (flow.vorticity_integrable time) (flow.vorticity_memLp time _) position).trans
    (add_le_add (mul_le_mul_of_nonneg_right four_bound ENNReal.toReal_nonneg)
      (mul_le_mul_of_nonneg_right one_bound (by positivity)))

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
