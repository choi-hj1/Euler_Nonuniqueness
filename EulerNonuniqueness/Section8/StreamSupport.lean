import EulerNonuniqueness.Section8.StreamVerticalDerivative

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem vectorTest_coordinate_support {test : ℝ × Plane → Plane} (compact : HasCompactSupport test) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ time position,
      (radius < |time| ∨ radius < |position.re| ∨ radius < |position.im|) → test (time, position) = 0 := by
  obtain ⟨radius, positive, bounded⟩ := compact.isCompact.isBounded.exists_pos_norm_le
  refine ⟨radius, positive, fun time position outside => ?_⟩
  apply image_eq_zero_of_nmem_tsupport
  intro member
  have estimate := bounded (time, position) member
  have coordinateBound : |time| ≤ ‖(time, position)‖ := by simpa only [Real.norm_eq_abs] using (norm_fst_le (time, position))
  have timeBound : |time| ≤ radius := coordinateBound.trans estimate
  have positionBound : ‖position‖ ≤ radius := (norm_snd_le (time, position)).trans estimate
  rcases outside with outside | outside | outside
  · exact (not_lt_of_ge timeBound) outside
  · exact (not_lt_of_ge ((Complex.abs_re_le_norm position).trans positionBound)) outside
  · exact (not_lt_of_ge ((Complex.abs_im_le_norm position).trans positionBound)) outside

theorem streamFunction_eq_zero_of_time_or_vertical
    {test : ℝ × Plane → Plane} {radius : ℝ}
    (supported : ∀ time position, (radius < |time| ∨ radius < |position.re| ∨ radius < |position.im|) →
      test (time, position) = 0) (point : ℝ × Plane) (outside : radius < |point.1| ∨ radius < |point.2.im|) :
    streamFunction test point = 0 := by
  rw [streamFunction_eq_integral_Iic]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun horizontal => by
    have zero := supported point.1 ((horizontal : ℂ) + (point.2.im : ℂ) * Complex.I) (by
      rcases outside with timeOutside | verticalOutside
      · exact Or.inl timeOutside
      · right; right; simpa using verticalOutside)
    simp only [horizontalTestSlice, zero, Complex.zero_im, Pi.zero_apply]

theorem streamFunction_eq_zero_of_horizontal_gt
    {test : ℝ × Plane → Plane} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (divergence : ∀ point, spatialDivergence test point = 0) {radius : ℝ} (positive : 0 < radius)
    (supported : ∀ time position, (radius < |time| ∨ radius < |position.re| ∨ radius < |position.im|) →
      test (time, position) = 0) (point : ℝ × Plane) (outside : radius < point.2.re) :
    streamFunction test point = 0 := by
  let curve := fun vertical : ℝ => (point.1, (point.2.re : ℂ) + (vertical : ℂ) * Complex.I)
  have curveDerivative (vertical : ℝ) : HasDerivAt curve (0, Complex.I) vertical := by
    have embedding := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt vertical (hasDerivAt_id vertical)
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
      (hasDerivAt_const vertical point.1).prodMk ((embedding.mul_const Complex.I).const_add (point.2.re : ℂ))
  have derivative (vertical : ℝ) : HasDerivAt (streamFunction test ∘ curve) 0 vertical := by
    have result := ((contDiff_streamFunction smooth compact).differentiable (by simp) (curve vertical)).hasFDerivAt.comp_hasDerivAt
      vertical (curveDerivative vertical)
    have testZero : test (curve vertical) = 0 := supported _ _ (Or.inr (Or.inl (by
      simpa only [curve, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using lt_of_lt_of_le outside (le_abs_self _))))
    have zero := spatialDerivative_streamFunction_vertical smooth compact divergence (curve vertical)
    simp only [testZero, Complex.zero_re, neg_zero] at zero
    change fderiv ℝ (streamFunction test) (curve vertical) (0, Complex.I) = 0 at zero
    simpa only [zero] using result
  have constant := is_const_of_deriv_eq_zero (fun vertical => (derivative vertical).differentiableAt)
    (fun vertical => (derivative vertical).deriv) point.2.im (radius + 1)
  have reconstruction : curve point.2.im = point := Prod.ext rfl point.2.re_add_im
  simp only [Function.comp_apply, reconstruction] at constant
  rw [constant]
  apply streamFunction_eq_zero_of_time_or_vertical supported
  right
  change radius < |(((point.2.re : ℂ) + ((radius + 1 : ℝ) : ℂ) * Complex.I)).im|
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  rw [abs_of_pos (by linarith : 0 < radius + 1)]
  linarith

end EulerNonuniqueness
