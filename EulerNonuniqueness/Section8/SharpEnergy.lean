import EulerNonuniqueness.Section8.SmoothDivCurl

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem memLp_component_fderiv_biotSavart {vorticity : Vorticity}
    (smooth : ContDiff ℝ ∞ vorticity) (compact : HasCompactSupport vorticity)
    (linear : Plane →L[ℝ] ℝ) (direction : Plane) :
    MemLp (fun position => fderiv ℝ (linear ∘ biotSavart vorticity) position direction) 2 volume := by
  have equality : (fun position => fderiv ℝ (linear ∘ biotSavart vorticity) position direction) =
      linear ∘ (fun position => fderiv ℝ (biotSavart vorticity) position direction) :=
    funext fun position => fderiv_realLinearMap_comp_apply
      (contDiff_biotSavart_of_contDiff_compactSupport smooth compact) linear position direction
  rw [equality]
  exact linear.comp_memLp' (memLp_fderiv_biotSavart_apply smooth compact direction)

theorem memLp_component_second_fderiv_biotSavart {vorticity : Vorticity}
    (smooth : ContDiff ℝ ∞ vorticity) (compact : HasCompactSupport vorticity)
    (linear : Plane →L[ℝ] ℝ) (firstDirection secondDirection : Plane) :
    MemLp (fun position => fderiv ℝ
      (fun point => fderiv ℝ (linear ∘ biotSavart vorticity) point firstDirection)
        position secondDirection) 2 volume := by
  have velocitySmooth := contDiff_biotSavart_of_contDiff_compactSupport smooth compact
  have firstEquality :
      (fun position => fderiv ℝ (linear ∘ biotSavart vorticity) position firstDirection) =
        linear ∘ (fun position => fderiv ℝ (biotSavart vorticity) position firstDirection) :=
    funext fun position => fderiv_realLinearMap_comp_apply velocitySmooth linear position firstDirection
  rw [firstEquality]
  have derivativeSmooth : ContDiff ℝ ∞
      (fun position => fderiv ℝ (biotSavart vorticity) position firstDirection) :=
    (velocitySmooth.fderiv_right (by simp)).clm_apply contDiff_const
  have secondEquality : (fun position => fderiv ℝ
      (linear ∘ (fun point => fderiv ℝ (biotSavart vorticity) point firstDirection))
        position secondDirection) =
      linear ∘ (fun position => fderiv ℝ
        (fun point => fderiv ℝ (biotSavart vorticity) point firstDirection) position secondDirection) :=
    funext fun position => fderiv_realLinearMap_comp_apply derivativeSmooth linear position secondDirection
  rw [secondEquality]
  exact linear.comp_memLp' (memLp_second_fderiv_biotSavart_apply smooth compact firstDirection secondDirection)

theorem integral_gradient_components_biotSavart_sq {vorticity : Vorticity}
    (smooth : ContDiff ℝ ∞ vorticity) (compact : HasCompactSupport vorticity)
    (zeroMean : (∫ position, vorticity position) = 0) :
    (∫ position,
      (fderiv ℝ (Complex.reCLM ∘ biotSavart vorticity) position 1) ^ 2 +
      (fderiv ℝ (Complex.reCLM ∘ biotSavart vorticity) position Complex.I) ^ 2 +
      (fderiv ℝ (Complex.imCLM ∘ biotSavart vorticity) position 1) ^ 2 +
      (fderiv ℝ (Complex.imCLM ∘ biotSavart vorticity) position Complex.I) ^ 2) =
        ∫ position, vorticity position ^ 2 := by
  have velocitySmooth := contDiff_biotSavart_of_contDiff_compactSupport smooth compact
  have cross := integral_cross_directionalDerivatives_of_memLp
    (Complex.reCLM.contDiff.comp velocitySmooth) (Complex.imCLM.contDiff.comp velocitySmooth)
    (Complex.reCLM.comp_memLp'
      (memLp_biotSavart_two_of_continuous_compactSupport_integral_zero smooth.continuous compact zeroMean))
    (memLp_component_fderiv_biotSavart smooth compact Complex.reCLM)
    (memLp_component_fderiv_biotSavart smooth compact Complex.imCLM)
    (memLp_component_second_fderiv_biotSavart smooth compact Complex.imCLM) 1 Complex.I
  rw [integral_divCurl_algebra_of_memLp
    (memLp_component_fderiv_biotSavart smooth compact Complex.reCLM 1)
    (memLp_component_fderiv_biotSavart smooth compact Complex.reCLM Complex.I)
    (memLp_component_fderiv_biotSavart smooth compact Complex.imCLM 1)
    (memLp_component_fderiv_biotSavart smooth compact Complex.imCLM Complex.I) cross]
  apply integral_congr_ae
  filter_upwards [] with position
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.imCLM_apply,
    divergence_biotSavart_smooth smooth compact, curl_biotSavart_smooth smooth compact,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]

theorem integral_gradient_biotSavart_sq {vorticity : Vorticity}
    (smooth : ContDiff ℝ ∞ vorticity) (compact : HasCompactSupport vorticity)
    (zeroMean : (∫ position, vorticity position) = 0) :
    (∫ position, ‖fderiv ℝ (biotSavart vorticity) position 1‖ ^ 2 +
      ‖fderiv ℝ (biotSavart vorticity) position Complex.I‖ ^ 2) =
        ∫ position, vorticity position ^ 2 := by
  rw [← integral_gradient_components_biotSavart_sq smooth compact zeroMean]
  apply integral_congr_ae
  filter_upwards [] with position
  simp only [fderiv_realLinearMap_comp_apply
    (contDiff_biotSavart_of_contDiff_compactSupport smooth compact),
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.sq_norm, Complex.normSq_apply]
  ring

end EulerNonuniqueness
