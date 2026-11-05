import EulerNonuniqueness.Section3.FiniteMovingPatchFamily

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

def dominator (family : FiniteMovingPatchFamily count) (radius : ℝ) (position : ℂ) : ℝ :=
  (Metric.closedBall (0 : ℂ) radius).indicator (fun _ => ∑ index : Fin count, |family.density index|) position

theorem dominator_nonnegative (family : FiniteMovingPatchFamily count) (radius : ℝ) (position : ℂ) :
    0 ≤ family.dominator radius position :=
  indicator_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) position

theorem dominator_memLp (family : FiniteMovingPatchFamily count) (radius : ℝ) (exponent : ℝ≥0∞) :
    MemLp (family.dominator radius) exponent volume :=
  memLp_indicator_const exponent measurableSet_closedBall _ (Or.inr (measure_closedBall_lt_top.ne))

theorem dominator_integrable (family : FiniteMovingPatchFamily count) (radius : ℝ) :
    Integrable (family.dominator radius) := memLp_one_iff_integrable.mp (family.dominator_memLp radius 1)

theorem norm_vorticity_le_dominator (family : FiniteMovingPatchFamily count) (time : ℝ) {radius : ℝ}
    (domainBound : ∀ index, (family.patch index).domain time ⊆ Metric.closedBall 0 radius) (position : ℂ) :
    ‖family.vorticity time position‖ ≤ family.dominator radius position := by
  by_cases member : position ∈ Metric.closedBall (0 : ℂ) radius
  · simpa only [dominator, indicator_of_mem member] using family.norm_vorticity_le_density_sum time position
  · have outside : ∀ index, position ∉ (family.patch index).domain time :=
      fun index inside => member (domainBound index inside)
    simp only [vorticity, patchVorticity, indicator_of_not_mem (outside _), Finset.sum_const_zero,
      norm_zero, dominator, indicator_of_not_mem member, le_refl]

def speedBound (family : FiniteMovingPatchFamily count) (radius : ℝ) : ℝ :=
  (eLpNorm (family.dominator radius) (ENNReal.ofReal (4 : ℝ)) volume).toReal *
    (eLpNorm ((Metric.ball (0 : ℂ) 1).indicator biotSavartKernel) (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
      (∫ position, family.dominator radius position) * (1 / (2 * Real.pi))

theorem speedBound_nonnegative (family : FiniteMovingPatchFamily count) (radius : ℝ) :
    0 ≤ family.speedBound radius :=
  add_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (mul_nonneg (integral_nonneg (family.dominator_nonnegative radius)) (by positivity))

theorem norm_biotSavart_le_speedBound (family : FiniteMovingPatchFamily count) (time : ℝ) {radius : ℝ}
    (domainBound : ∀ index, (family.patch index).domain time ⊆ Metric.closedBall 0 radius) (position : ℂ) :
    ‖biotSavart (family.vorticity time) position‖ ≤ family.speedBound radius := by
  have fourBound : (eLpNorm (family.vorticity time) (ENNReal.ofReal (4 : ℝ)) volume).toReal ≤
      (eLpNorm (family.dominator radius) (ENNReal.ofReal (4 : ℝ)) volume).toReal :=
    ENNReal.toReal_mono (family.dominator_memLp radius _).2.ne
      (eLpNorm_mono_real (family.norm_vorticity_le_dominator time domainBound))
  have oneBound : (∫ position, ‖family.vorticity time position‖) ≤ ∫ position, family.dominator radius position :=
    integral_mono (family.vorticity_integrable time).norm (family.dominator_integrable radius)
      (family.norm_vorticity_le_dominator time domainBound)
  exact (norm_biotSavart_le_L1_L4 (family.vorticity_integrable time) (family.vorticity_memLp time _) position).trans
    (add_le_add (mul_le_mul_of_nonneg_right fourBound ENNReal.toReal_nonneg)
      (mul_le_mul_of_nonneg_right oneBound (by positivity)))

theorem exists_uniform_speed_bound (family : FiniteMovingPatchFamily count) {horizon : ℝ}
    (nonnegative : 0 ≤ horizon) : ∃ speed : ℝ, 0 ≤ speed ∧
      ∀ time ∈ Icc 0 horizon, ∀ position, ‖biotSavart (family.vorticity time) position‖ ≤ speed := by
  obtain ⟨radius, _, domainBound⟩ := family.exists_uniform_domain_bound nonnegative
  exact ⟨family.speedBound radius, family.speedBound_nonnegative radius,
    fun time inside position => family.norm_biotSavart_le_speedBound time (domainBound time inside) position⟩

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
