import EulerNonuniqueness.Section3.ContourAntiholomorphicFunctional
import EulerNonuniqueness.Section3.ContourPolynomialGaugeMoments

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem contourAntiholomorphicFunctional_const (data : PeriodicC1HolderHalf) (value : ℂ) :
    contourAntiholomorphicFunctional (fun _ => value) data =
      value * (contourAreaFunctional data : ℂ) := by
  have area := contourPolynomialMoment_conjugate_integral data 0
  rw [contourPolynomialMoment_zero_real] at area
  simp only [pow_zero, mul_one, Complex.star_def, Complex.conj_ofReal] at area
  unfold contourAntiholomorphicFunctional
  calc
    _ = (Complex.I / 2) * (value * ∫ label in (-Real.pi)..Real.pi,
        data.val.1 label * star (data.val.2.val.1 label)) := by
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro label _
      ring
    _ = value * ((Complex.I / 2) * ∫ label in (-Real.pi)..Real.pi,
        data.val.1 label * star (data.val.2.val.1 label)) := by ring
    _ = _ := congrArg (fun result : ℂ => value * result)
      (by simpa only [starRingEnd_apply] using area.symm)

theorem contourAntiholomorphicFunctional_mul_const (data : PeriodicC1HolderHalf)
    (kernel : ℂ → ℂ) (value : ℂ) :
    contourAntiholomorphicFunctional (fun position => value * kernel position) data =
      value * contourAntiholomorphicFunctional kernel data := by
  unfold contourAntiholomorphicFunctional
  have identity : (fun label => data.val.1 label * (value * kernel (data.val.1 label)) *
      star (data.val.2.val.1 label)) =
      fun label => value * (data.val.1 label * kernel (data.val.1 label) * star (data.val.2.val.1 label)) := by
    funext label
    ring
  rw [identity, intervalIntegral.integral_const_mul]
  ring

theorem contourAntiholomorphicFunctional_add (data : PeriodicC1HolderHalf)
    (first second : ℂ → ℂ)
    (firstContinuous : Continuous (fun label => first (data.val.1 label)))
    (secondContinuous : Continuous (fun label => second (data.val.1 label))) :
    contourAntiholomorphicFunctional (fun position => first position + second position) data =
      contourAntiholomorphicFunctional first data + contourAntiholomorphicFunctional second data := by
  unfold contourAntiholomorphicFunctional
  have identity : (fun label => data.val.1 label * (first (data.val.1 label) + second (data.val.1 label)) *
      star (data.val.2.val.1 label)) =
      fun label => data.val.1 label * first (data.val.1 label) * star (data.val.2.val.1 label) +
        data.val.1 label * second (data.val.1 label) * star (data.val.2.val.1 label) := by
    funext label
    ring
  rw [identity, intervalIntegral.integral_add
    (((data.val.1.continuous.mul firstContinuous).mul data.val.2.val.1.continuous.star).intervalIntegrable _ _)
    (((data.val.1.continuous.mul secondContinuous).mul data.val.2.val.1.continuous.star).intervalIntegrable _ _)]
  ring

theorem contourAntiholomorphicFunctional_add_const (data : PeriodicC1HolderHalf)
    (kernel : ℂ → ℂ) (value : ℂ)
    (kernelContinuous : Continuous (fun label => kernel (data.val.1 label))) :
    contourAntiholomorphicFunctional (fun position => kernel position + value) data =
      contourAntiholomorphicFunctional kernel data + value * (contourAreaFunctional data : ℂ) := by
  rw [contourAntiholomorphicFunctional_add data kernel (fun _ => value) kernelContinuous continuous_const,
    contourAntiholomorphicFunctional_const]

end EulerNonuniqueness.Paper
