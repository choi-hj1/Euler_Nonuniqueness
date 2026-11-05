import EulerNonuniqueness.Section3.ContourPolynomialCentroidGauge

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance projectedPolynomialJetC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem areaNormalizedAntiholomorphicForcing_analyticAt (degree : ℕ) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    AnalyticAt ℝ (areaNormalizedAntiholomorphicForcing degree) data := by
  have head := (c1ConjugateCLM.analyticAt (x := c1NaturalPower data (degree + 1))).comp
    (f := fun current : PeriodicC1HolderHalf => c1NaturalPower current (degree + 1))
    (c1NaturalPower_analyticAt (degree + 1) data)
  have numerator := ((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).analyticAt
    (x := contourPolynomialMoment (degree + 1) data)).comp
    (f := contourPolynomialMoment (degree + 1)) (analyticAt_contourPolynomialMoment (degree + 1) data)
  have denominator := (Complex.ofRealCLM.analyticAt (x := contourAreaFunctional data)).comp
    (f := contourAreaFunctional) (analyticAt_contourAreaFunctional data)
  have nonzero : (contourAreaFunctional data : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (contourAreaFunctional_pos data small).ne'
  have quotient := numerator.fun_div denominator nonzero
  have tail := (c1ConstantCLM.analyticAt (x := star (contourPolynomialMoment (degree + 1) data) /
    (contourAreaFunctional data : ℂ))).comp
    (f := fun current : PeriodicC1HolderHalf => star (contourPolynomialMoment (degree + 1) current) /
      (contourAreaFunctional current : ℂ)) quotient
  exact head.sub tail

theorem projectedPolynomialForcing_circle_firstJet (degree : ℕ) (coefficient : ℂ) :
    fderiv ℝ (fun data : PeriodicC1HolderHalf => contourCentroidGaugeProjection data
      (coefficient • c1Conjugate (c1NaturalPower data (degree + 1)))) standardCircleBanach =
      (c1ProductCLM (c1Constant coefficient)).comp
        (fderiv ℝ (centeredAntiholomorphicForcing degree) standardCircleBanach) := by
  have identity : (fun data : PeriodicC1HolderHalf => contourCentroidGaugeProjection data
      (coefficient • c1Conjugate (c1NaturalPower data (degree + 1)))) =ᶠ[𝓝 standardCircleBanach]
      fun data => c1ProductCLM (c1Constant coefficient) (areaNormalizedAntiholomorphicForcing degree data) := by
    filter_upwards [Metric.ball_mem_nhds standardCircleBanach (show (0 : ℝ) < 1 / 3 by norm_num)] with data nearby
    rw [Metric.mem_ball, dist_eq_norm] at nearby
    rw [contourCentroidGaugeProjection_complexPolynomial data degree coefficient nearby]
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rfl
  have small : ‖standardCircleBanach - standardCircleBanach‖ < (1 / 3 : ℝ) := by norm_num
  have inner := (areaNormalizedAntiholomorphicForcing_analyticAt degree standardCircleBanach small).differentiableAt.hasFDerivAt
  have actual := (c1ProductCLM (c1Constant coefficient)).hasFDerivAt.comp standardCircleBanach inner
  have derivativeIdentity := actual.fderiv
  change fderiv ℝ (fun data => c1ProductCLM (c1Constant coefficient) (areaNormalizedAntiholomorphicForcing degree data))
      standardCircleBanach = _ at derivativeIdentity
  rw [identity.fderiv_eq, derivativeIdentity, areaNormalizedAntiholomorphicForcing_firstJet]

end EulerNonuniqueness.Paper
