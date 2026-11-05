import EulerNonuniqueness.Definitions

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem tsupport_separableTest_subset {temporal : ℝ → ℝ} {spatial : Plane → ℝ} :
    tsupport (fun point : ℝ × Plane => temporal point.1 * spatial point.2) ⊆
      tsupport temporal ×ˢ tsupport spatial := by
  apply closure_minimal
  · intro point inside
    have nonzero : temporal point.1 * spatial point.2 ≠ 0 := inside
    exact ⟨subset_closure (left_ne_zero_of_mul nonzero),
      subset_closure (right_ne_zero_of_mul nonzero)⟩
  · exact (isClosed_tsupport temporal).prod (isClosed_tsupport spatial)

theorem scalarTestOn_separable {horizon : ℝ} {temporal : ℝ → ℝ}
    {spatial : Plane → ℝ} (temporalSmooth : ContDiff ℝ ∞ temporal)
    (temporalCompact : HasCompactSupport temporal)
    (temporalSupport : tsupport temporal ⊆ Ioo 0 horizon)
    (spatialSmooth : ContDiff ℝ ∞ spatial) (spatialCompact : HasCompactSupport spatial) :
    ScalarTestOn horizon (fun point : ℝ × Plane => temporal point.1 * spatial point.2) := by
  refine ⟨(temporalSmooth.comp contDiff_fst).mul (spatialSmooth.comp contDiff_snd), ?_, ?_⟩
  · exact (temporalCompact.isCompact.prod spatialCompact.isCompact).of_isClosed_subset
      (isClosed_tsupport _) tsupport_separableTest_subset
  · intro time position afterHorizon
    have temporalZero : temporal time = 0 := by
      apply image_eq_zero_of_nmem_tsupport
      exact fun inside => not_lt_of_ge afterHorizon (temporalSupport inside).2
    simp only [temporalZero, zero_mul]

theorem timeDerivative_separable {temporal : ℝ → ℝ} {spatial : Plane → ℝ}
    (temporalDifferentiable : Differentiable ℝ temporal)
    (spatialDifferentiable : Differentiable ℝ spatial) (point : ℝ × Plane) :
    timeDerivative (fun point : ℝ × Plane => temporal point.1 * spatial point.2) point =
      deriv temporal point.1 * spatial point.2 := by
  change (fderiv ℝ (fun point => (temporal ∘ Prod.fst) point *
    (spatial ∘ Prod.snd) point) point) (1, 0) = _
  rw [fderiv_mul
    ((temporalDifferentiable point.1).comp point differentiableAt_fst)
    ((spatialDifferentiable point.2).comp point differentiableAt_snd)]
  rw [fderiv_comp point (temporalDifferentiable point.1) differentiableAt_fst,
    fderiv_comp point (spatialDifferentiable point.2) differentiableAt_snd]
  simp [fderiv_fst, fderiv_snd, fderiv_deriv, mul_comm]

theorem spatialDerivative_separable {temporal : ℝ → ℝ} {spatial : Plane → ℝ}
    (temporalDifferentiable : Differentiable ℝ temporal)
    (spatialDifferentiable : Differentiable ℝ spatial) (point : ℝ × Plane) (direction : Plane) :
    spatialDerivative (fun point : ℝ × Plane => temporal point.1 * spatial point.2)
      point direction = temporal point.1 * fderiv ℝ spatial point.2 direction := by
  change (fderiv ℝ (fun point => (temporal ∘ Prod.fst) point *
    (spatial ∘ Prod.snd) point) point) (0, direction) = _
  rw [fderiv_mul
    ((temporalDifferentiable point.1).comp point differentiableAt_fst)
    ((spatialDifferentiable point.2).comp point differentiableAt_snd)]
  rw [fderiv_comp point (temporalDifferentiable point.1) differentiableAt_fst,
    fderiv_comp point (spatialDifferentiable point.2) differentiableAt_snd]
  simp [fderiv_fst, fderiv_snd]

end EulerNonuniqueness
