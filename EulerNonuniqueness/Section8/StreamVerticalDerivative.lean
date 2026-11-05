import EulerNonuniqueness.Section8.StreamCompatibility
import EulerNonuniqueness.Section8.TestSlices

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem fderiv_vector_spatial_component {test : ℝ × Plane → Plane} (smooth : ContDiff ℝ ∞ test)
    (component : Plane →L[ℝ] ℝ) (time : ℝ) (position direction : Plane) :
    fderiv ℝ (fun other => component (test (time, other))) position direction =
      component (spatialDerivative test (time, position) direction) := by
  have slice := ((smooth.differentiable (by simp)) (time, position)).hasFDerivAt.comp position
    ((hasFDerivAt_const (time : ℝ) position).prodMk (hasFDerivAt_id position))
  have derivative := component.hasFDerivAt.comp position slice
  change fderiv ℝ (component ∘ test ∘ Prod.mk time) position direction = _
  rw [derivative.fderiv]
  rfl

theorem fderiv_streamFunction_eq_zero_of_horizontal_lt {test : ℝ × Plane → Plane}
    {radius : ℝ} (supported : ∀ point horizontal, horizontal ∉ Metric.closedBall (0 : ℝ) radius →
      horizontalTestSlice test point horizontal = 0) (point : ℝ × Plane)
    (outside : point.2.re < -radius) : fderiv ℝ (streamFunction test) point = 0 := by
  have neighborhood : ∀ᶠ other : ℝ × Plane in 𝓝 point, other.2.re < -radius :=
    (isOpen_lt (Complex.continuous_re.comp continuous_snd) continuous_const).mem_nhds outside
  have equality : streamFunction test =ᶠ[𝓝 point] (fun _ => (0 : ℝ)) := by
    filter_upwards [neighborhood] with other negative
    exact streamFunction_eq_zero_of_horizontal_lt supported other negative
  simpa only [fderiv_const] using equality.fderiv_eq (𝕜 := ℝ)

theorem spatialDerivative_streamFunction_vertical {test : ℝ × Plane → Plane}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (divergence : ∀ point, spatialDivergence test point = 0) (point : ℝ × Plane) :
    spatialDerivative (streamFunction test) point Complex.I = -(test point).re := by
  have potentialSmooth := contDiff_spatial_slice (contDiff_streamFunction smooth compact) point.1
  have sliceSmooth : ContDiff ℝ ∞ (fun position : Plane => test (point.1, position)) :=
    smooth.comp (contDiff_const.prodMk contDiff_id)
  have firstSmooth := Complex.reCLM.contDiff.comp sliceSmooth
  have secondSmooth := Complex.imCLM.contDiff.comp sliceSmooth
  have horizontal (position : Plane) : fderiv ℝ (fun other => streamFunction test (point.1, other)) position 1 =
      (test (point.1, position)).im := by
    rw [fderiv_spatial_slice (contDiff_streamFunction smooth compact)]
    exact spatialDerivative_streamFunction_horizontal smooth compact _
  have spatialDivergence (position : Plane) :
      fderiv ℝ (fun other => (test (point.1, other)).re) position 1 +
        fderiv ℝ (fun other => (test (point.1, other)).im) position Complex.I = 0 := by
    change fderiv ℝ (fun other => Complex.reCLM (test (point.1, other))) position 1 +
      fderiv ℝ (fun other => Complex.imCLM (test (point.1, other))) position Complex.I = 0
    rw [fderiv_vector_spatial_component smooth Complex.reCLM, fderiv_vector_spatial_component smooth Complex.imCLM]
    exact divergence (point.1, position)
  obtain ⟨radius, positive, bounded⟩ := (compact.isCompact.image continuous_snd).isBounded.exists_pos_norm_le
  have vectorSupported (other : ℝ × Plane) (horizontal : ℝ)
      (outside : horizontal ∉ Metric.closedBall (0 : ℝ) radius) :
      test (other.1, (horizontal : ℂ) + (other.2.im : ℂ) * Complex.I) = 0 := by
    apply image_eq_zero_of_nmem_tsupport
    intro member
    apply outside
    have estimate := bounded _ ⟨_, member, rfl⟩
    have coordinate := Complex.abs_re_le_norm ((horizontal : ℂ) + (other.2.im : ℂ) * Complex.I)
    have bound : |horizontal| ≤ radius := by simpa using coordinate.trans estimate
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using bound
  have supported (other : ℝ × Plane) (horizontal : ℝ)
      (outside : horizontal ∉ Metric.closedBall (0 : ℝ) radius) : horizontalTestSlice test other horizontal = 0 := by
    simp only [horizontalTestSlice, vectorSupported other horizontal outside, Complex.zero_im]
  have base (vertical : ℝ) : ∃ horizontal : ℝ,
      fderiv ℝ (fun other => streamFunction test (point.1, other)) ((horizontal : ℂ) + (vertical : ℂ) * Complex.I) Complex.I +
        (test (point.1, (horizontal : ℂ) + (vertical : ℂ) * Complex.I)).re = 0 := by
    refine ⟨-radius - 1, ?_⟩
    let position : Plane := ((-radius - 1 : ℝ) : ℂ) + (vertical : ℂ) * Complex.I
    have negative : position.re < -radius := by simp [position]
    have derivativeZero := fderiv_streamFunction_eq_zero_of_horizontal_lt supported (point.1, position) negative
    have testZero : test (point.1, position) = 0 := by
      have equality := vectorSupported (point.1, position) (-radius - 1) (by
        simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
        rw [abs_of_neg (by linarith : -radius - 1 < 0)]
        linarith)
      simpa [position] using equality
    change fderiv ℝ (fun other => streamFunction test (point.1, other)) position Complex.I + (test (point.1, position)).re = 0
    rw [fderiv_spatial_slice (contDiff_streamFunction smooth compact)]
    simp only [spatialDerivative, derivativeZero, ContinuousLinearMap.zero_apply, testZero, Complex.zero_re, add_zero]
  have result := stream_vertical_derivative_of_compatibility potentialSmooth firstSmooth secondSmooth horizontal spatialDivergence base point.2
  rw [fderiv_spatial_slice (contDiff_streamFunction smooth compact)] at result
  exact result

end EulerNonuniqueness
