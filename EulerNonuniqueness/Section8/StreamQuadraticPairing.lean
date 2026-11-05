import EulerNonuniqueness.Section8.StreamCurlPairing
import EulerNonuniqueness.Section8.SmoothQuadraticIntegral

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology ContDiff InnerProductSpace

namespace EulerNonuniqueness

theorem inner_linear_complex_expand (linear : Plane →L[ℝ] Plane) (velocity : Plane) :
    ⟪velocity, linear velocity⟫_ℝ = velocity.re ^ 2 * (linear 1).re +
      velocity.re * velocity.im * ((linear Complex.I).re + (linear 1).im) +
        velocity.im ^ 2 * (linear Complex.I).im := by
  have split : velocity = velocity.re • (1 : Plane) + velocity.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using velocity.re_add_im.symm
  have image := congrArg linear split
  rw [map_add, map_smul, map_smul] at image
  rw [image, real_inner_eq_re_inner, RCLike.inner_apply]
  change ((velocity.re • linear 1 + velocity.im • linear Complex.I) * (starRingEnd ℂ) velocity).re = _
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, zero_mul, sub_zero, zero_add]
  ring

theorem inner_vectorTest_advection_eq_neg_transportQuadratic {test : ℝ × Plane → Plane}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (divergence : ∀ point, spatialDivergence test point = 0) (time : ℝ) (position velocity : Plane) :
    ⟪velocity, spatialDerivative test (time, position) velocity⟫_ℝ =
      -transportQuadratic (fun _ => velocity.re) (fun _ => velocity.im)
        (fun other => streamFunction test (time, other)) position := by
  let potential := fun other => streamFunction test (time, other)
  have potentialSmooth : ContDiff ℝ ∞ potential := contDiff_spatial_slice (contDiff_streamFunction smooth compact) time
  have horizontal : (fun other => (test (time, other)).im) = (fun other => fderiv ℝ potential other 1) := by
    funext other
    rw [fderiv_spatial_slice (contDiff_streamFunction smooth compact)]
    exact (spatialDerivative_streamFunction_horizontal smooth compact _).symm
  have vertical : (fun other => (test (time, other)).re) = (fun other => -fderiv ℝ potential other Complex.I) := by
    funext other
    have equality := spatialDerivative_streamFunction_vertical smooth compact divergence (time, other)
    rw [← fderiv_spatial_slice (contDiff_streamFunction smooth compact)] at equality
    linarith
  have realDerivative (direction : Plane) : (spatialDerivative test (time, position) direction).re =
      -fderiv ℝ (fun other => fderiv ℝ potential other Complex.I) position direction := by
    have component := fderiv_vector_spatial_component smooth Complex.reCLM time position direction
    change fderiv ℝ (fun other => (test (time, other)).re) position direction = _ at component
    rw [vertical, fderiv_neg, ContinuousLinearMap.neg_apply] at component
    exact component.symm
  have imaginaryDerivative (direction : Plane) : (spatialDerivative test (time, position) direction).im =
      fderiv ℝ (fun other => fderiv ℝ potential other 1) position direction := by
    have component := fderiv_vector_spatial_component smooth Complex.imCLM time position direction
    change fderiv ℝ (fun other => (test (time, other)).im) position direction = _ at component
    rw [horizontal] at component
    exact component.symm
  have expansion := inner_linear_complex_expand
    ((fderiv ℝ test (time, position)).comp (ContinuousLinearMap.inr ℝ ℝ Plane)) velocity
  change ⟪velocity, spatialDerivative test (time, position) velocity⟫_ℝ =
    velocity.re ^ 2 * (spatialDerivative test (time, position) 1).re +
      velocity.re * velocity.im * ((spatialDerivative test (time, position) Complex.I).re + (spatialDerivative test (time, position) 1).im) +
        velocity.im ^ 2 * (spatialDerivative test (time, position) Complex.I).im at expansion
  rw [expansion, realDerivative, realDerivative, imaginaryDerivative, imaginaryDerivative]
  rw [mixed_directionalDerivatives_commute potentialSmooth Complex.I 1 position]
  dsimp only [transportQuadratic]
  ring

end EulerNonuniqueness
