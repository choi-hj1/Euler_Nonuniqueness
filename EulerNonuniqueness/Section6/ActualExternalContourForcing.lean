import EulerNonuniqueness.Section3.SpatialContourComposition
import EulerNonuniqueness.Section6.MovingExternalPatchDerivative

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper

def FinitePatchEvolution.externalSpatialContourField
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (center : ℂ) (radiusPositive : 0 < radius)
    (distance : Fin count → ℝ) (strain hessian : ℝ≥0)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ position ∈ Metric.closedBall center (4 * radius),
      ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ motion.domain time source patch,
      distance source ≤ ‖position - location‖)
    (strainBound : (∑ source ∈ Finset.univ.erase index,
      2 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 2)) ≤ (strain : ℝ))
    (hessianBound : (∑ source ∈ Finset.univ.erase index,
      4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) ≤ (hessian : ℝ)) :
    SpatialContourField center radius where
  field := biotSavart (externalPatchVorticity scales motion time index)
  derivative := fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index))
  strain := strain
  hessian := hessian
  hasFDerivAt := by
    intro position member
    have largeMember := Metric.closedBall_subset_closedBall (by linarith : 3 * radius ≤ 4 * radius) member
    exact (evolution.externalPatch_biotSavart_hasFDerivAt inside index distance positive
      (separated position largeMember)).differentiableAt.hasFDerivAt
  derivative_bound := by
    intro position member
    have lipschitz := evolution.externalPatch_biotSavart_lipschitzOn inside amplitudePositive frequencyPositive
      ratioPositive index distance (Metric.closedBall center (4 * radius)) positive separated strainBound
    have neighborhood : Metric.closedBall center (4 * radius) ∈ nhds position := by
      apply Metric.closedBall_mem_nhds_of_mem
      change dist position center < 4 * radius
      have distanceBound : dist position center ≤ 3 * radius := member
      linarith
    exact norm_fderiv_le_of_lipschitzOn ℝ neighborhood lipschitz
  derivative_lipschitz := by
    apply evolution.externalPatch_biotSavart_fderiv_lipschitzOn inside amplitudePositive frequencyPositive
      ratioPositive index distance (Metric.closedBall center (3 * radius)) positive _ hessianBound
    intro position member
    exact separated position (Metric.closedBall_subset_closedBall (by linarith : 3 * radius ≤ 4 * radius) member)

theorem FinitePatchEvolution.externalSpatialContourField_value
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (center : ℂ) (radiusPositive : 0 < radius)
    (distance : Fin count → ℝ) (strain hessian : ℝ≥0)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ position ∈ Metric.closedBall center (4 * radius),
      ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ motion.domain time source patch,
      distance source ≤ ‖position - location‖)
    (strainBound : (∑ source ∈ Finset.univ.erase index,
      2 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 2)) ≤ (strain : ℝ))
    (hessianBound : (∑ source ∈ Finset.univ.erase index,
      4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) ≤ (hessian : ℝ))
    (data : PeriodicC1HolderHalf) (phase : Circle) (bound : ‖data‖ ≤ 3) (label : ℝ) :
    ((evolution.externalSpatialContourField inside amplitudePositive frequencyPositive ratioPositive index center
      radiusPositive distance strain hessian positive separated strainBound hessianBound).rawRotatedCompose
        data phase radiusPositive bound).val.1 label =
      radius⁻¹ • ((phase : ℂ)⁻¹ * biotSavart (externalPatchVorticity scales motion time index)
        (center + radius • ((phase : ℂ) * data.val.1 label))) :=
  SpatialContourField.rawRotatedCompose_value _ data phase radiusPositive bound label

end EulerNonuniqueness.Paper
