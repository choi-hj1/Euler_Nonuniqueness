import EulerNonuniqueness.Section3.ContourAnalyticCentroid
import EulerNonuniqueness.Section3.ComplexHolderBanach
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

local instance centroidRotationC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem contourPolynomialMoment_unit_smul (degree : ℕ) (data : PeriodicC1HolderHalf) (phase : Circle) :
    contourPolynomialMoment degree ((phase : ℂ) • data) =
      (phase : ℂ) ^ degree * contourPolynomialMoment degree data := by
  have unit : (phase : ℂ) * star (phase : ℂ) = (1 : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    norm_num
  rw [contourPolynomialMoment_eq_integral, contourPolynomialMoment_eq_integral]
  have integrand : (fun label => (((phase : ℂ) • data).val.1 label) ^ degree *
      star (((phase : ℂ) • data).val.1 label) * (((phase : ℂ) • data).val.2.val.1 label)) =
      fun label => (phase : ℂ) ^ degree *
        (data.val.1 label ^ degree * star (data.val.1 label) * data.val.2.val.1 label) := by
    funext label
    change ((phase : ℂ) * data.val.1 label) ^ degree * star ((phase : ℂ) * data.val.1 label) *
      ((phase : ℂ) * data.val.2.val.1 label) = _
    rw [mul_pow, star_mul]
    calc
      _ = ((phase : ℂ) * star (phase : ℂ)) * ((phase : ℂ) ^ degree *
        (data.val.1 label ^ degree * star (data.val.1 label) * data.val.2.val.1 label)) := by ring
      _ = _ := by rw [unit, one_mul]
  rw [integrand, intervalIntegral.integral_const_mul]
  ring

theorem contourAreaFunctional_unit_smul (data : PeriodicC1HolderHalf) (phase : Circle) :
    contourAreaFunctional ((phase : ℂ) • data) = contourAreaFunctional data := by
  simp only [contourAreaFunctional, contourPolynomialMoment_unit_smul, pow_zero, one_mul]

theorem contourCentroidFunctional_unit_smul (data : PeriodicC1HolderHalf) (phase : Circle) :
    contourCentroidFunctional ((phase : ℂ) • data) = (phase : ℂ) * contourCentroidFunctional data := by
  rw [contourCentroidFunctional, contourPolynomialMoment_unit_smul,
    contourAreaFunctional_unit_smul, pow_one, contourCentroidFunctional, mul_div_assoc]

set_option maxHeartbeats 1000000 in
theorem contourCentroidFunctional_derivative_rotation (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    (fderiv ℝ contourCentroidFunctional data) (Complex.I • data) =
      Complex.I * contourCentroidFunctional data := by
  have exponential : HasDerivAt (fun time : ℝ => Complex.exp (Complex.I * (time : ℂ))) Complex.I 0 := by
    simpa using ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul Complex.I).cexp)
  have pathDerivative : HasDerivAt (fun time : ℝ => Complex.exp (Complex.I * (time : ℂ)) • data)
      (Complex.I • data) 0 := exponential.smul_const data
  have centroidDerivative := (analyticAt_contourCentroidFunctional data small).differentiableAt.hasFDerivAt
  have chain : HasDerivAt (fun time : ℝ => contourCentroidFunctional
      (Complex.exp (Complex.I * (time : ℂ)) • data))
      ((fderiv ℝ contourCentroidFunctional data) (Complex.I • data)) 0 := by
    have atInitial : HasFDerivAt contourCentroidFunctional (fderiv ℝ contourCentroidFunctional data)
        (Complex.exp (Complex.I * ((0 : ℝ) : ℂ)) • data) := by
      simpa using centroidDerivative
    exact HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf) (E := ℂ)
      (f := fun time : ℝ => Complex.exp (Complex.I * (time : ℂ)) • data)
      (0 : ℝ) atInitial pathDerivative
  have identity : (fun time : ℝ => contourCentroidFunctional (Complex.exp (Complex.I * (time : ℂ)) • data)) =
      fun time : ℝ => Complex.exp (Complex.I * (time : ℂ)) * contourCentroidFunctional data := by
    funext time
    simpa only [Circle.coe_exp, mul_comm] using contourCentroidFunctional_unit_smul data (Circle.exp time)
  rw [identity] at chain
  exact chain.unique (exponential.mul_const (contourCentroidFunctional data))

end EulerNonuniqueness.Paper
