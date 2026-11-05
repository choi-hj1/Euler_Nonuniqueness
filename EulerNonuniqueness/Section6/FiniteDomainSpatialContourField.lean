import EulerNonuniqueness.Section3.SpatialContourComposition
import EulerNonuniqueness.Section6.MovingPatchHessian
import EulerNonuniqueness.Section6.MovingPatchFieldBounds

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Section6

def finiteDomainSourceField {index : Type*} (selected : Finset index)
    (domain : index → Set ℂ) (density : index → ℝ) (position : ℂ) : ℂ :=
  ∑ source ∈ selected, biotSavart ((domain source).indicator (fun _ => density source)) position

theorem finiteDomainSourceField_hasFDerivAt {index : Type*} (selected : Finset index)
    (domain : index → Set ℂ) (density distance : index → ℝ)
    (measurable : ∀ source ∈ selected, MeasurableSet (domain source))
    (finite : ∀ source ∈ selected, volume (domain source) < ⊤)
    (positive : ∀ source ∈ selected, 0 < distance source) {position : ℂ}
    (separated : ∀ source ∈ selected, ∀ location ∈ domain source, distance source ≤ ‖position - location‖) :
    HasFDerivAt (finiteDomainSourceField selected domain density)
      (∑ source ∈ selected, fderiv ℝ (biotSavart ((domain source).indicator (fun _ => density source))) position) position := by
  exact HasFDerivAt.sum (fun source member =>
    (indicator_biotSavart_hasFDerivAt_of_separation (measurable source member) (finite source member)
      (density source) (positive source member) (separated source member)).differentiableAt.hasFDerivAt)

def finiteDomainSpatialContourField {index : Type*} (selected : Finset index)
    (domain : index → Set ℂ) (density distance : index → ℝ)
    (center : ℂ) {radius : ℝ} (radiusPositive : 0 < radius) (strain hessian : ℝ≥0)
    (measurable : ∀ source ∈ selected, MeasurableSet (domain source))
    (finite : ∀ source ∈ selected, volume (domain source) < ⊤)
    (positive : ∀ source ∈ selected, 0 < distance source)
    (separated : ∀ position ∈ Metric.closedBall center (4 * radius), ∀ source ∈ selected,
      ∀ location ∈ domain source, distance source ≤ ‖position - location‖)
    (strainBound : (∑ source ∈ selected,
      |density source| * volume.real (domain source) / (2 * Real.pi * distance source ^ 2)) ≤ (strain : ℝ))
    (hessianBound : (∑ source ∈ selected,
      |density source| * volume.real (domain source) / (Real.pi * distance source ^ 3)) ≤ (hessian : ℝ)) :
    Paper.SpatialContourField center radius where
  field := finiteDomainSourceField selected domain density
  derivative := fderiv ℝ (finiteDomainSourceField selected domain density)
  strain := strain
  hessian := hessian
  hasFDerivAt := by
    intro position member
    exact (finiteDomainSourceField_hasFDerivAt selected domain density distance measurable finite positive
      (separated position (Metric.closedBall_subset_closedBall (by linarith : 3 * radius ≤ 4 * radius) member))).differentiableAt.hasFDerivAt
  derivative_bound := by
    intro position member
    have lipschitz : LipschitzOnWith strain (finiteDomainSourceField selected domain density)
        (Metric.closedBall center (4 * radius)) := by
      apply lipschitzOnWith_iff_norm_sub_le.mpr
      intro first firstInside second secondInside
      rw [finiteDomainSourceField, finiteDomainSourceField, ← Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      have estimate := Finset.sum_le_sum (fun source membership =>
        indicator_biotSavart_difference_bound (measurable source membership) (finite source membership)
          (density source) (positive source membership) (separated first firstInside source membership)
          (separated second secondInside source membership))
      rw [← Finset.sum_mul] at estimate
      exact estimate.trans (mul_le_mul_of_nonneg_right strainBound (norm_nonneg _))
    apply norm_fderiv_le_of_lipschitzOn ℝ _ lipschitz
    apply Metric.closedBall_mem_nhds_of_mem
    change dist position center < 4 * radius
    have distanceBound : dist position center ≤ 3 * radius := member
    linarith
  derivative_lipschitz := by
    apply lipschitzOnWith_iff_norm_sub_le.mpr
    intro first firstInside second secondInside
    have firstSeparated := separated first
      (Metric.closedBall_subset_closedBall (by linarith : 3 * radius ≤ 4 * radius) firstInside)
    have secondSeparated := separated second
      (Metric.closedBall_subset_closedBall (by linarith : 3 * radius ≤ 4 * radius) secondInside)
    rw [(finiteDomainSourceField_hasFDerivAt selected domain density distance measurable finite positive firstSeparated).fderiv,
      (finiteDomainSourceField_hasFDerivAt selected domain density distance measurable finite positive secondSeparated).fderiv,
      ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    have estimate := Finset.sum_le_sum (fun source membership =>
      indicator_biotSavart_fderiv_difference_bound (measurable source membership) (finite source membership)
        (density source) (positive source membership) (firstSeparated source membership) (secondSeparated source membership))
    have expansion : (∑ source ∈ selected,
        |density source| * volume.real (domain source) * ‖first - second‖ / (Real.pi * distance source ^ 3)) =
        (∑ source ∈ selected,
          |density source| * volume.real (domain source) / (Real.pi * distance source ^ 3)) * ‖first - second‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro source _
      ring
    rw [expansion] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right hessianBound (norm_nonneg _))

end EulerNonuniqueness.Section6
