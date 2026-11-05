import EulerNonuniqueness.Section3.MovingMaterialPatchWeakTransport
import EulerNonuniqueness.Section8.MeasurableKernelConvolution

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

structure FiniteMovingPatchFamily (count : ℕ) where
  patch : Fin count → MovingMaterialPatch
  density : Fin count → ℝ

namespace MovingMaterialPatch

theorem domain_subset_ball (path : MovingMaterialPatch) (time : ℝ) :
    path.domain time ⊆ Metric.ball (path.center time) (2 * path.radius) := by
  rintro position ⟨normalized, member, rfl⟩
  have bound := nearCircleInterior_subset_ball (path.shape time) (path.nearby time) member
  have normalizedBound : ‖normalized‖ < 2 := by
    have strict : ‖normalized‖ < 1 + ‖path.shape time - standardCircleBanach‖ := by
      simpa only [Metric.mem_ball, dist_zero_right] using bound
    linarith [path.nearby time]
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos path.radius_positive, norm_mul, Circle.norm_coe, one_mul]
  nlinarith [path.radius_positive]

end MovingMaterialPatch

namespace FiniteMovingPatchFamily

variable {count : ℕ}

def patchVorticity (family : FiniteMovingPatchFamily count) (time : ℝ) (index : Fin count) : Vorticity :=
  ((family.patch index).domain time).indicator (fun _ => family.density index)

def vorticity (family : FiniteMovingPatchFamily count) (time : ℝ) (position : ℂ) : ℝ :=
  ∑ index : Fin count, family.patchVorticity time index position

theorem patchVorticity_memLp (family : FiniteMovingPatchFamily count) (time : ℝ) (index : Fin count)
    (exponent : ℝ≥0∞) : MemLp (family.patchVorticity time index) exponent volume :=
  memLp_indicator_const exponent ((family.patch index).domain_isOpen time).measurableSet _
    (Or.inr ((family.patch index).domain_isBounded time).measure_lt_top.ne)

theorem patchVorticity_integrable (family : FiniteMovingPatchFamily count) (time : ℝ) (index : Fin count) :
    Integrable (family.patchVorticity time index) := memLp_one_iff_integrable.mp (family.patchVorticity_memLp time index 1)

theorem vorticity_memLp (family : FiniteMovingPatchFamily count) (time : ℝ) (exponent : ℝ≥0∞) :
    MemLp (family.vorticity time) exponent volume :=
  memLp_finset_sum Finset.univ fun index _ => family.patchVorticity_memLp time index exponent

theorem vorticity_integrable (family : FiniteMovingPatchFamily count) (time : ℝ) : Integrable (family.vorticity time) :=
  memLp_one_iff_integrable.mp (family.vorticity_memLp time 1)

theorem measurable_patchVorticity (family : FiniteMovingPatchFamily count) (index : Fin count) :
    Measurable (fun point : ℝ × ℂ => family.patchVorticity point.1 index point.2) := by
  have result := (family.patch index).measurable_domain_indicator.const_mul (family.density index)
  convert result using 1
  funext point
  by_cases member : point.2 ∈ (family.patch index).domain point.1 <;> simp [patchVorticity, member]

theorem measurable_vorticity (family : FiniteMovingPatchFamily count) :
    Measurable (fun point : ℝ × ℂ => family.vorticity point.1 point.2) := by
  change Measurable (fun point : ℝ × ℂ => ∑ index : Fin count, family.patchVorticity point.1 index point.2)
  exact Finset.measurable_sum _ fun index _ => family.measurable_patchVorticity index

theorem measurable_biotSavart (family : FiniteMovingPatchFamily count) :
    Measurable (fun point : ℝ × ℂ => biotSavart (family.vorticity point.1) point.2) :=
  measurable_biotSavart_of_measurable_vorticity family.measurable_vorticity

theorem norm_vorticity_le_density_sum (family : FiniteMovingPatchFamily count) (time : ℝ) (position : ℂ) :
    ‖family.vorticity time position‖ ≤ ∑ index : Fin count, |family.density index| := by
  unfold vorticity
  apply (norm_sum_le Finset.univ _).trans
  apply Finset.sum_le_sum
  intro index _
  by_cases member : position ∈ (family.patch index).domain time
  · simp [patchVorticity, member, Real.norm_eq_abs]
  · simp only [patchVorticity, indicator_of_not_mem member, norm_zero]
    exact abs_nonneg _

theorem exists_uniform_domain_bound (family : FiniteMovingPatchFamily count) {horizon : ℝ}
    (nonnegative : 0 ≤ horizon) : ∃ radius : ℝ, 0 < radius ∧
      ∀ time ∈ Icc 0 horizon, ∀ index : Fin count, (family.patch index).domain time ⊆ Metric.closedBall 0 radius := by
  let total : ℝ → ℝ := fun time => ∑ index : Fin count, (‖(family.patch index).center time‖ + 2 * (family.patch index).radius)
  have totalContinuous : Continuous total :=
    continuous_finset_sum _ fun index _ => (family.patch index).center_continuous.norm.add continuous_const
  obtain ⟨maximumTime, maximumInside, maximal⟩ := isCompact_Icc.exists_isMaxOn
    ⟨0, le_rfl, nonnegative⟩ totalContinuous.continuousOn
  refine ⟨total maximumTime + 1, ?_, ?_⟩
  · have nonnegativeTotal : 0 ≤ total maximumTime := Finset.sum_nonneg fun index _ =>
      add_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) (family.patch index).radius_positive.le)
    linarith
  · intro time inside index position member
    have distanceBound := (family.patch index).domain_subset_ball time member
    have coordinateBound : ‖(family.patch index).center time‖ + 2 * (family.patch index).radius ≤ total time := by
      exact Finset.single_le_sum (fun other _ => add_nonneg (norm_nonneg ((family.patch other).center time))
        (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (family.patch other).radius_positive.le)) (Finset.mem_univ index)
    have triangle : ‖position‖ ≤ ‖position - (family.patch index).center time‖ + ‖(family.patch index).center time‖ := by
      calc
        ‖position‖ = ‖(position - (family.patch index).center time) + (family.patch index).center time‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have strict : ‖position - (family.patch index).center time‖ < 2 * (family.patch index).radius := by
      simpa only [Metric.mem_ball, dist_eq_norm] using distanceBound
    rw [Metric.mem_closedBall, dist_zero_right]
    have timeBound : total time ≤ total maximumTime := maximal inside
    exact (triangle.trans (add_le_add_right strict.le _)).trans
      ((by linarith : 2 * (family.patch index).radius + ‖(family.patch index).center time‖ ≤ total time).trans
        (timeBound.trans (by linarith)))

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
