import EulerNonuniqueness.Section3.ContourPolynomialCentroidGauge
import EulerNonuniqueness.Section3.CentroidStrainFixedRelabel

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance complexStrainGaugeC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem contourCentroidGaugeProjection_complex_strain (data : PeriodicC1HolderHalf) (coefficient : ℂ)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    contourCentroidGaugeProjection data (coefficient • c1Conjugate data) =
      coefficient • centroidCenteredStrain data := by
  have powerOne : c1NaturalPower data (0 + 1) = data := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rw [c1NaturalPower_value, pow_one]
  have identity := contourCentroidGaugeProjection_complexPolynomial data 0 coefficient small
  rw [powerOne] at identity
  have normalized : areaNormalizedAntiholomorphicForcing 0 data = centroidCenteredStrain data := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change star ((c1NaturalPower data (0 + 1)).val.1 label) -
        star (contourPolynomialMoment (0 + 1) data) / (contourAreaFunctional data : ℂ) =
      star (data.val.1 label) - star (contourPolynomialMoment 1 data / (contourAreaFunctional data : ℂ))
    rw [powerOne, star_div₀]
    simp only [Complex.star_def, Complex.conj_ofReal]
  exact identity.trans (congrArg (fun direction : PeriodicC1HolderHalf => coefficient • direction) normalized)

theorem contourCentroidGaugeProjection_complex_strain_fderiv
    (data : PeriodicC1HolderHalf) (coefficient : ℂ)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    fderiv ℝ (fun current : PeriodicC1HolderHalf => contourCentroidGaugeProjection current
      (coefficient • c1Conjugate current)) data =
      (c1ProductCLM (c1Constant coefficient)).comp (fderiv ℝ centroidCenteredStrain data) := by
  have inner := (centroidCenteredStrain_analyticAt data small).differentiableAt.hasFDerivAt
  have actual := (c1ProductCLM (c1Constant coefficient)).hasFDerivAt.comp data inner
  have equality : (fun current : PeriodicC1HolderHalf => contourCentroidGaugeProjection current
      (coefficient • c1Conjugate current)) =ᶠ[𝓝 data]
      (fun current => c1ProductCLM (c1Constant coefficient) (centroidCenteredStrain current)) := by
    have nearby : ∀ᶠ current in 𝓝 data, ‖current - standardCircleBanach‖ < 1 / 3 :=
      (isOpen_lt ((continuous_id.sub continuous_const).norm) continuous_const).mem_nhds small
    filter_upwards [nearby] with current close
    rw [contourCentroidGaugeProjection_complex_strain current coefficient close]
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rfl
  exact (actual.congr_of_eventuallyEq equality).fderiv

end EulerNonuniqueness.Paper
