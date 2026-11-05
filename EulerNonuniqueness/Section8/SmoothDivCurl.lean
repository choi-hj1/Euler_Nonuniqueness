import EulerNonuniqueness.Section8.DivCurlEnergy
import EulerNonuniqueness.Section8.SmoothBiotSavart
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem realLinearMap_apply_complex (linear : Plane →L[ℝ] ℝ) (position : Plane) :
    linear position = position.re * linear 1 + position.im * linear Complex.I := by
  have split : position = position.re • (1 : ℂ) + position.im • Complex.I := by
    simp only [Complex.real_smul, mul_one]
    exact position.re_add_im.symm
  calc
    linear position = linear (position.re • (1 : ℂ) + position.im • Complex.I) := congrArg linear split
    _ = _ := by rw [map_add, map_smul, map_smul]; rfl

theorem integral_test_directionalDerivative {function : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ function) {test : Plane → ℝ}
    (testSmooth : ContDiff ℝ ∞ test) (testCompact : HasCompactSupport test) (direction : Plane) :
    (∫ position, test position * fderiv ℝ function position direction) =
      -(∫ position, fderiv ℝ test position direction * function position) := by
  have functionDerivative := contDiff_directionalDerivative smooth direction
  have testDerivative := contDiff_directionalDerivative testSmooth direction
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    ((testDerivative.continuous.mul smooth.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_right (testCompact.fderiv_apply ℝ direction)))
    ((testSmooth.continuous.mul functionDerivative.continuous).integrable_of_hasCompactSupport
      testCompact.mul_right)
    ((testSmooth.continuous.mul smooth.continuous).integrable_of_hasCompactSupport
      testCompact.mul_right)
    (testSmooth.differentiable (by simp)) (smooth.differentiable (by simp))

theorem scalar_divergence_eq_of_weak {first second source : Plane → ℝ}
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second)
    (sourceContinuous : Continuous source)
    (weak : ∀ test : Plane → ℝ, ContDiff ℝ ∞ test → HasCompactSupport test →
      (∫ position, fderiv ℝ test position (first position + second position * Complex.I)) =
        -(∫ position, test position * source position)) :
    ∀ position, fderiv ℝ first position 1 + fderiv ℝ second position Complex.I = source position := by
  have firstDerivative := contDiff_directionalDerivative firstSmooth 1
  have secondDerivative := contDiff_directionalDerivative secondSmooth Complex.I
  have continuousDivergence : Continuous (fun position =>
      fderiv ℝ first position 1 + fderiv ℝ second position Complex.I) :=
    firstDerivative.continuous.add secondDerivative.continuous
  have almostEverywhere := ae_eq_of_integral_contDiff_smul_eq (μ := volume)
    continuousDivergence.locallyIntegrable sourceContinuous.locallyIntegrable
    (fun test testSmooth testCompact => by
      have testFirstDerivative := contDiff_directionalDerivative testSmooth 1
      have testSecondDerivative := contDiff_directionalDerivative testSmooth Complex.I
      have firstIntegrable : Integrable (fun position =>
          test position * fderiv ℝ first position 1) :=
        (testSmooth.continuous.mul firstDerivative.continuous).integrable_of_hasCompactSupport
          testCompact.mul_right
      have secondIntegrable : Integrable (fun position =>
          test position * fderiv ℝ second position Complex.I) :=
        (testSmooth.continuous.mul secondDerivative.continuous).integrable_of_hasCompactSupport
          testCompact.mul_right
      have firstPairIntegrable : Integrable (fun position =>
          fderiv ℝ test position 1 * first position) :=
        (testFirstDerivative.continuous.mul firstSmooth.continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.mul_right (testCompact.fderiv_apply ℝ 1))
      have secondPairIntegrable : Integrable (fun position =>
          fderiv ℝ test position Complex.I * second position) :=
        (testSecondDerivative.continuous.mul secondSmooth.continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.mul_right (testCompact.fderiv_apply ℝ Complex.I))
      have pairing : (∫ position, fderiv ℝ test position
          (first position + second position * Complex.I)) =
          (∫ position, fderiv ℝ test position 1 * first position) +
            ∫ position, fderiv ℝ test position Complex.I * second position := by
        rw [← integral_add firstPairIntegrable secondPairIntegrable]
        apply integral_congr_ae
        filter_upwards [] with position
        rw [realLinearMap_apply_complex]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
        ring
      simp_rw [smul_eq_mul, mul_add]
      rw [integral_add firstIntegrable secondIntegrable,
        integral_test_directionalDerivative firstSmooth testSmooth testCompact,
        integral_test_directionalDerivative secondSmooth testSmooth testCompact]
      linarith only [pairing, weak test testSmooth testCompact])
  exact fun position => congrFun
    (MeasureTheory.Measure.eq_of_ae_eq almostEverywhere continuousDivergence sourceContinuous) position

theorem divergence_biotSavart_smooth {vorticity : Vorticity}
    (smooth : ContDiff ℝ ∞ vorticity) (compact : HasCompactSupport vorticity) (position : Plane) :
    fderiv ℝ (fun point => (biotSavart vorticity point).re) position 1 +
      fderiv ℝ (fun point => (biotSavart vorticity point).im) position Complex.I = 0 := by
  have velocitySmooth := contDiff_biotSavart_of_contDiff_compactSupport smooth compact
  obtain ⟨radius, _, bound⟩ := compact.isCompact.isBounded.exists_pos_norm_le
  have supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius := by
    intro source nonzero
    simpa using bound source (subset_tsupport _ nonzero)
  apply scalar_divergence_eq_of_weak
    (Complex.reCLM.contDiff.comp velocitySmooth) (Complex.imCLM.contDiff.comp velocitySmooth)
    (source := fun _ => 0) continuous_const _ position
  intro test testSmooth testCompact
  simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.re_add_im, mul_zero, integral_zero, neg_zero] using
    (divergenceFree_biotSavart_of_integrable_support
      (smooth.continuous.integrable_of_hasCompactSupport compact)
      supportBound (testSmooth.of_le (by simp)) testCompact).2

theorem curl_biotSavart_smooth {vorticity : Vorticity}
    (smooth : ContDiff ℝ ∞ vorticity) (compact : HasCompactSupport vorticity) (position : Plane) :
    fderiv ℝ (fun point => (biotSavart vorticity point).im) position 1 -
      fderiv ℝ (fun point => (biotSavart vorticity point).re) position Complex.I = vorticity position := by
  have velocitySmooth := contDiff_biotSavart_of_contDiff_compactSupport smooth compact
  obtain ⟨radius, _, bound⟩ := compact.isCompact.isBounded.exists_pos_norm_le
  have supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius := by
    intro source nonzero
    simpa using bound source (subset_tsupport _ nonzero)
  have divergence := scalar_divergence_eq_of_weak
    (Complex.imCLM.contDiff.comp velocitySmooth).neg (Complex.reCLM.contDiff.comp velocitySmooth)
    (source := fun point => -vorticity point) smooth.continuous.neg
    (fun test testSmooth testCompact => by
      have vectorEquality : ∀ point : Plane,
          ((-(biotSavart vorticity point).im : ℝ) : ℂ) +
            (biotSavart vorticity point).re * Complex.I = Complex.I * biotSavart vorticity point := by
        intro point
        apply Complex.ext <;> simp
      simp only [Pi.neg_apply, Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
      simp_rw [vectorEquality]
      simpa only [mul_neg, integral_neg, neg_neg, mul_comm] using
        (curl_biotSavart_of_integrable_support
          (smooth.continuous.integrable_of_hasCompactSupport compact)
          supportBound testSmooth testCompact).2) position
  simp only [fderiv_neg, ContinuousLinearMap.neg_apply, Function.comp_def,
    Complex.reCLM_apply, Complex.imCLM_apply] at divergence
  linarith only [divergence]

end EulerNonuniqueness
