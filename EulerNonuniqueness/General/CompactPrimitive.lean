import Mathlib

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

theorem exists_contDiff_compact_primitive_of_support_Ioo {function : ℝ → ℝ} {lower upper : ℝ}
    (smooth : ContDiff ℝ ∞ function)
    (supportInside : Function.support function ⊆ Ioo lower upper)
    (zeroMean : (∫ point, function point) = 0) :
    ∃ primitive : ℝ → ℝ, ContDiff ℝ ∞ primitive ∧ HasCompactSupport primitive ∧
      tsupport primitive ⊆ Icc lower upper ∧
      ∀ point, HasDerivAt primitive (function point) point := by
  let primitive : ℝ → ℝ := fun point => ∫ source in lower..point, function source
  have derivative (point : ℝ) : HasDerivAt primitive (function point) point :=
    intervalIntegral.integral_hasDerivAt_right (smooth.continuous.intervalIntegrable lower point)
      smooth.continuous.stronglyMeasurable.stronglyMeasurableAtFilter smooth.continuous.continuousAt
  have primitiveSmooth : ContDiff ℝ ∞ primitive := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun point => (derivative point).differentiableAt, ?_⟩
    have equality : deriv primitive = function := funext fun point => (derivative point).deriv
    rw [equality]
    exact smooth
  have zeroLeft {point : ℝ} (before : point ≤ lower) : primitive point = 0 := by
    dsimp only [primitive]
    rw [intervalIntegral.integral_symm]
    have zeroIntegral : (∫ source in point..lower, function source) =
        ∫ source in point..lower, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro source inside
      rw [uIcc_of_le before] at inside
      by_contra nonzero
      exact not_lt_of_ge inside.2 (supportInside nonzero).1
    rw [zeroIntegral, intervalIntegral.integral_zero, neg_zero]
  have zeroRight {point : ℝ} (after : upper ≤ point) : primitive point = 0 := by
    dsimp only [primitive]
    rw [intervalIntegral.integral_eq_integral_of_support_subset, zeroMean]
    intro source nonzero
    exact ⟨(supportInside nonzero).1, (supportInside nonzero).2.le.trans after⟩
  have primitiveSupport : Function.support primitive ⊆ Icc lower upper := by
    intro point nonzero
    by_cases before : point ≤ lower
    · exact False.elim (nonzero (zeroLeft before))
    · by_cases after : upper ≤ point
      · exact False.elim (nonzero (zeroRight after))
      · exact ⟨(lt_of_not_ge before).le, (lt_of_not_ge after).le⟩
  exact ⟨primitive, primitiveSmooth,
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc primitiveSupport,
    closure_minimal primitiveSupport isClosed_Icc, derivative⟩

theorem exists_contDiff_compact_primitive {function : ℝ → ℝ}
    (smooth : ContDiff ℝ ∞ function) (compact : HasCompactSupport function)
    (zeroMean : (∫ point, function point) = 0) :
    ∃ primitive : ℝ → ℝ, ContDiff ℝ ∞ primitive ∧ HasCompactSupport primitive ∧
      ∀ point, HasDerivAt primitive (function point) point := by
  obtain ⟨radius, radiusPositive, bounded⟩ := compact.isCompact.isBounded.exists_pos_norm_le
  have supportInside : Function.support function ⊆ Ioo (-(radius + 1)) (radius + 1) := by
    intro point nonzero
    have bound := bounded point (subset_tsupport _ nonzero)
    rw [Real.norm_eq_abs, abs_le] at bound
    constructor <;> linarith
  obtain ⟨primitive, primitiveSmooth, primitiveCompact, _, derivative⟩ :=
    exists_contDiff_compact_primitive_of_support_Ioo smooth supportInside zeroMean
  exact ⟨primitive, primitiveSmooth, primitiveCompact, derivative⟩
