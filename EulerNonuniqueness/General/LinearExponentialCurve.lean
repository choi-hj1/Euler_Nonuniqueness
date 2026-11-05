import Mathlib
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv

namespace EulerNonuniqueness.General

noncomputable section

open MeasureTheory

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

def linearExponentialCurve (operator : Space →L[ℝ] Space) (initial : Space) (time : ℝ) : Space :=
  (NormedSpace.exp ℝ (time • operator)) initial

theorem linearExponentialCurve_zero (operator : Space →L[ℝ] Space) (initial : Space) :
    linearExponentialCurve operator initial 0 = initial := by
  simp [linearExponentialCurve]

theorem linearExponentialCurve_hasDerivAt (operator : Space →L[ℝ] Space) (initial : Space) (time : ℝ) :
    HasDerivAt (linearExponentialCurve operator initial)
      (operator (linearExponentialCurve operator initial time)) time := by
  have actual := (hasDerivAt_exp_smul_const' operator time).clm_apply (hasDerivAt_const time initial)
  change HasDerivAt (fun current : ℝ => (NormedSpace.exp ℝ (current • operator)) initial)
    (operator ((NormedSpace.exp ℝ (time • operator)) initial)) time
  simpa only [ContinuousLinearMap.mul_apply, map_zero, add_zero] using actual

theorem linearExponentialCurve_analyticAt (operator : Space →L[ℝ] Space) (initial : Space) (time : ℝ) :
    AnalyticAt ℝ (linearExponentialCurve operator initial) time := by
  let scaling : ℝ →L[ℝ] (Space →L[ℝ] Space) := (ContinuousLinearMap.id ℝ ℝ).smulRight operator
  let evaluation : (Space →L[ℝ] Space) →L[ℝ] Space := ContinuousLinearMap.apply ℝ Space initial
  have inner : AnalyticAt ℝ (fun current : ℝ => current • operator) time := scaling.analyticAt (x := time)
  have middle : AnalyticAt ℝ (fun current : ℝ => NormedSpace.exp ℝ (current • operator)) time :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (time • operator)).comp
      (f := fun current : ℝ => current • operator) inner
  exact (evaluation.analyticAt (x := NormedSpace.exp ℝ (time • operator))).comp
    (f := fun current : ℝ => NormedSpace.exp ℝ (current • operator)) middle

theorem linearExponentialCurve_second_hasDerivAt (operator : Space →L[ℝ] Space) (initial : Space) (time : ℝ) :
    HasDerivAt (fun current => operator (linearExponentialCurve operator initial current))
      (operator (operator (linearExponentialCurve operator initial time))) time :=
  operator.hasFDerivAt.comp_hasDerivAt time (linearExponentialCurve_hasDerivAt operator initial time)

theorem complex_linear_ode_eq_exp {trajectory : ℝ → ℂ} (coefficient : ℂ)
    (equation : ∀ time, HasDerivAt trajectory (coefficient * trajectory time) time) (time : ℝ) :
    trajectory time = Complex.exp ((time : ℂ) * coefficient) * trajectory 0 := by
  let adjusted := fun current : ℝ => Complex.exp (-(current : ℂ) * coefficient) * trajectory current
  have adjustedDerivative (current : ℝ) : HasDerivAt adjusted 0 current := by
    have exponent := ((hasDerivAt_id current).ofReal_comp.neg.mul_const coefficient).cexp
    have actual := exponent.mul (equation current)
    apply actual.congr_deriv
    simp only [neg_mul, one_mul, Complex.ofReal_one]
    ring
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun current _ => adjustedDerivative current)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume 0 time)
  have constant : adjusted time = trajectory 0 := by
    simpa only [intervalIntegral.integral_zero, adjusted, Complex.ofReal_zero, neg_zero, zero_mul,
      Complex.exp_zero, one_mul, sub_eq_zero] using integral.symm
  calc
    trajectory time = Complex.exp ((time : ℂ) * coefficient) * adjusted time := by
      dsimp only [adjusted]
      rw [← mul_assoc, ← Complex.exp_add]
      simp
    _ = _ := by rw [constant]

theorem linearExponentialCurve_evaluation (operator : Space →L[ℝ] Space) (initial : Space)
    (evaluation : Space →L[ℝ] ℂ) (coefficient : ℂ)
    (intertwines : ∀ value, evaluation (operator value) = coefficient * evaluation value) (time : ℝ) :
    evaluation (linearExponentialCurve operator initial time) =
      Complex.exp ((time : ℂ) * coefficient) * evaluation initial := by
  have actual (current : ℝ) : HasDerivAt (fun parameter => evaluation (linearExponentialCurve operator initial parameter))
      (coefficient * evaluation (linearExponentialCurve operator initial current)) current := by
    have result := evaluation.hasFDerivAt.comp_hasDerivAt current
      (linearExponentialCurve_hasDerivAt operator initial current)
    simpa only [intertwines] using result
  simpa only [linearExponentialCurve_zero] using complex_linear_ode_eq_exp coefficient actual time

end

end EulerNonuniqueness.General
