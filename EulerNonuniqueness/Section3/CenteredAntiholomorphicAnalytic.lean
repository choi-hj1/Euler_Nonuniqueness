import EulerNonuniqueness.Section3.CenteredAntiholomorphicForcing

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance centeredAnalyticC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem centeredAntiholomorphicForcing_analyticAt (degree : ℕ) (data : PeriodicC1HolderHalf) :
    AnalyticAt ℝ (centeredAntiholomorphicForcing degree) data := by
  have power := (ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf) c1ConjugateCLM (c1NaturalPower data (degree + 1))).comp
      (f := fun current : PeriodicC1HolderHalf => c1NaturalPower current (degree + 1))
      (c1NaturalPower_analyticAt (degree + 1) data)
  have conjugate := ((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).analyticAt
    (x := contourPolynomialMoment (degree + 1) data)).comp
    (f := contourPolynomialMoment (degree + 1)) (analyticAt_contourPolynomialMoment (degree + 1) data)
  have quotient : AnalyticAt ℝ (fun current : PeriodicC1HolderHalf =>
      star (contourPolynomialMoment (degree + 1) current) / (Real.pi : ℂ)) data :=
    conjugate.fun_div (analyticAt_const (v := (Real.pi : ℂ))) (by exact_mod_cast Real.pi_ne_zero)
  have constant := (ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := ℂ)
    (F := PeriodicC1HolderHalf) c1ConstantCLM
    (star (contourPolynomialMoment (degree + 1) data) / (Real.pi : ℂ))).comp
      (f := fun current : PeriodicC1HolderHalf => star (contourPolynomialMoment (degree + 1) current) / (Real.pi : ℂ)) quotient
  exact power.sub constant

end

end EulerNonuniqueness.Paper
