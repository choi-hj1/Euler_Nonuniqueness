import EulerNonuniqueness.Section3.ContourCirclePositiveMoments
import EulerNonuniqueness.Section3.CentroidCenteredStrainJet
import EulerNonuniqueness.General.ZeroNumeratorNonlinearCenteredJet

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance areaNormalizedForcingJetC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

def areaNormalizedAntiholomorphicForcing (degree : ℕ) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  c1Conjugate (c1NaturalPower data (degree + 1)) -
    c1Constant (star (contourPolynomialMoment (degree + 1) data) / (contourAreaFunctional data : ℂ))

theorem areaNormalizedAntiholomorphicForcing_eq_on_area (degree : ℕ) (data : PeriodicC1HolderHalf)
    (area : contourAreaFunctional data = Real.pi) :
    areaNormalizedAntiholomorphicForcing degree data = centeredAntiholomorphicForcing degree data := by
  unfold areaNormalizedAntiholomorphicForcing centeredAntiholomorphicForcing
  rw [area]

theorem areaNormalizedAntiholomorphicForcing_firstJet (degree : ℕ) :
    fderiv ℝ (areaNormalizedAntiholomorphicForcing degree) standardCircleBanach =
      fderiv ℝ (centeredAntiholomorphicForcing degree) standardCircleBanach := by
  let numerator := fun data : PeriodicC1HolderHalf => star (contourPolynomialMoment (degree + 1) data)
  let head := fun data : PeriodicC1HolderHalf => c1Conjugate (c1NaturalPower data (degree + 1))
  have headAnalytic : AnalyticAt ℝ head standardCircleBanach :=
    (c1ConjugateCLM.analyticAt (x := c1NaturalPower standardCircleBanach (degree + 1))).comp
      (f := fun data : PeriodicC1HolderHalf => c1NaturalPower data (degree + 1))
      (c1NaturalPower_analyticAt (degree + 1) standardCircleBanach)
  have numeratorAnalytic : AnalyticAt ℝ numerator standardCircleBanach :=
    ((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).analyticAt
      (x := contourPolynomialMoment (degree + 1) standardCircleBanach)).comp
      (f := contourPolynomialMoment (degree + 1)) (analyticAt_contourPolynomialMoment (degree + 1) standardCircleBanach)
  have denominatorAnalytic : AnalyticAt ℝ complexContourAreaFunction standardCircleBanach :=
    (Complex.ofRealCLM.analyticAt (x := contourAreaFunctional standardCircleBanach)).comp
      (f := contourAreaFunctional) (analyticAt_contourAreaFunctional standardCircleBanach)
  have nonzero : complexContourAreaFunction standardCircleBanach ≠ 0 := by
    change (contourAreaFunctional standardCircleBanach : ℂ) ≠ 0
    rw [contourAreaFunctional_standardCircle]
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have numeratorZero : numerator standardCircleBanach = 0 := by
    simp only [numerator, contourPolynomialMoment_circle_positive, star_zero]
  have result := EulerNonuniqueness.General.zeroNumerator_nonlinearCenteredField_firstJet head c1ConstantCLM
    numerator complexContourAreaFunction standardCircleBanach headAnalytic.differentiableAt
    numeratorAnalytic.differentiableAt denominatorAnalytic.differentiableAt nonzero numeratorZero
  have variableIdentity : (fun current => head current -
      c1ConstantCLM (numerator current / complexContourAreaFunction current)) =
      areaNormalizedAntiholomorphicForcing degree := rfl
  have fixedIdentity : (fun current => head current -
      c1ConstantCLM (numerator current / complexContourAreaFunction standardCircleBanach)) =
      centeredAntiholomorphicForcing degree := by
    funext current
    change c1Conjugate (c1NaturalPower current (degree + 1)) -
      c1Constant (star (contourPolynomialMoment (degree + 1) current) /
        (contourAreaFunctional standardCircleBanach : ℂ)) = _
    rw [contourAreaFunctional_standardCircle]
    rfl
  rw [variableIdentity, fixedIdentity] at result
  exact result

end

end EulerNonuniqueness.Paper
