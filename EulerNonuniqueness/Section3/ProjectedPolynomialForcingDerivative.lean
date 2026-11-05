import EulerNonuniqueness.Section3.ProjectedPolynomialForcingJet

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] projectedPolynomialJetC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem projectedPolynomialForcing_analyticAt (degree : ℕ) (coefficient : ℂ)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    AnalyticAt ℝ (fun current : PeriodicC1HolderHalf => contourCentroidGaugeProjection current
      (coefficient • c1Conjugate (c1NaturalPower current (degree + 1)))) data := by
  have outer : AnalyticAt ℝ (c1ProductCLM (c1Constant coefficient))
      (areaNormalizedAntiholomorphicForcing degree data) :=
    (c1ProductCLM (c1Constant coefficient)).analyticAt (areaNormalizedAntiholomorphicForcing degree data)
  have actual := outer.comp (f := areaNormalizedAntiholomorphicForcing degree)
    (areaNormalizedAntiholomorphicForcing_analyticAt degree data small)
  have neighborhood : ∀ᶠ current in 𝓝 data, ‖current - standardCircleBanach‖ < 1 / 3 :=
    (isOpen_lt ((continuous_id.sub continuous_const).norm) continuous_const).mem_nhds small
  apply actual.congr
  filter_upwards [neighborhood] with current currentSmall
  rw [contourCentroidGaugeProjection_complexPolynomial current degree coefficient currentSmall]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

theorem projectedPolynomialForcing_hasFDerivAt (degree : ℕ) (coefficient : ℂ)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    HasFDerivAt (fun current : PeriodicC1HolderHalf => contourCentroidGaugeProjection current
      (coefficient • c1Conjugate (c1NaturalPower current (degree + 1))))
      (fderiv ℝ (fun current : PeriodicC1HolderHalf => contourCentroidGaugeProjection current
        (coefficient • c1Conjugate (c1NaturalPower current (degree + 1)))) data) data :=
  (projectedPolynomialForcing_analyticAt degree coefficient data small).differentiableAt.hasFDerivAt

end EulerNonuniqueness.Paper
