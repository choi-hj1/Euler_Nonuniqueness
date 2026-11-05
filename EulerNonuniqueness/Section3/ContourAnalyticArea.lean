import EulerNonuniqueness.Section3.ContourAnalyticMoments

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def contourAreaFunctional (data : PeriodicC1HolderHalf) : ℝ := (contourPolynomialMoment 0 data).re

theorem analyticAt_contourAreaFunctional (data : PeriodicC1HolderHalf) :
    AnalyticAt ℝ contourAreaFunctional data :=
  (Complex.reCLM.analyticAt (x := contourPolynomialMoment 0 data)).comp
    (f := contourPolynomialMoment 0) (analyticAt_contourPolynomialMoment 0 data)

theorem contourAreaFunctional_eq_boundary (data : PeriodicC1HolderHalf) :
    contourAreaFunctional data = (1 / 2 : ℝ) *
      ∫ label in (-Real.pi)..Real.pi, contourAreaPair (data.val.1 label) (data.val.2.val.1 label) := by
  have integrable : IntervalIntegrable (fun label => star (data.val.1 label) * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi :=
    (data.val.1.continuous.star.mul data.val.2.val.1.continuous).intervalIntegrable _ _
  have coefficient : ∀ value : ℂ, (-Complex.I / 2 * value).re = (1 / 2 : ℝ) * value.im := by
    intro value
    simp [Complex.mul_re, Complex.div_re, Complex.div_im]
    ring
  unfold contourAreaFunctional
  rw [contourPolynomialMoment_eq_integral]
  simp only [pow_zero, one_mul]
  rw [coefficient]
  congr 1
  change Complex.imCLM (∫ label in (-Real.pi)..Real.pi, star (data.val.1 label) * data.val.2.val.1 label) = _
  rw [← Complex.imCLM.intervalIntegral_comp_comm integrable]
  rfl

theorem contourAreaFunctional_eq_domain_area (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    contourAreaFunctional data = (volume (nearCircleInterior data small)).toReal := by
  have green := integral_nearCircleInterior_divergence data small (fun position => position)
    (fun _ => ContinuousLinearMap.id ℝ ℂ) continuous_id continuous_const
    (fun position => hasFDerivAt_id (𝕜 := ℝ) position)
  have boundary_identity :
      (∫ label in (-Real.pi)..Real.pi, contourAreaPair (data.val.1 label) (data.val.2.val.1 label)) =
        2 * (volume (nearCircleInterior data small)).toReal := by
    rw [← green]
    simp only [contourPlaneTrace, ContinuousLinearMap.id_apply, Complex.one_re, Complex.I_im, one_add_one_eq_two,
      setIntegral_const, smul_eq_mul, measureReal_def]
    ring
  rw [contourAreaFunctional_eq_boundary, boundary_identity]
  ring

end

end EulerNonuniqueness.Paper
