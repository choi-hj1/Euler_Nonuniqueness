import EulerNonuniqueness.Section3.NormalizedExteriorCenteredFunctional
import EulerNonuniqueness.Section3.DiskSpectralFunctionalPairGeometry

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  c1InverseAnalyticOperatorGroup c1InverseAnalyticOperatorSpace
  antiholomorphicPairOperatorGroup antiholomorphicPairOperatorSpace

theorem exteriorCenteredSourceFunctional_exists_spectral_relative_ball :
    ∃ radius > (0 : ℝ), ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ initial final : PeriodicC1HolderHalf, initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      contourCentroidFunctional (diskPhysicalSpectralChart initial) = 0 →
      contourCentroidFunctional (diskPhysicalSpectralChart final) = 0 →
      ∀ parameter : ℂ, ‖parameter‖ ≤ parameterRadius → ∀ power : ℕ,
      ‖contourAntiholomorphicFunctional (normalizedExteriorInversePowerKernel parameter power)
          (diskPhysicalSpectralChart initial) -
        contourAntiholomorphicFunctional (normalizedExteriorInversePowerKernel parameter power)
          (diskPhysicalSpectralChart final)‖ ≤ constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ ^ 2 *
        (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
            ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
  obtain ⟨radius, radiusPositive, geometryConstant, geometryNonnegative, geometryBound⟩ :=
    diskPhysicalSpectral_exists_functional_pair_geometry
  obtain ⟨functionalRadius, functionalPositive, functionalConstant, functionalOne, functionalBound⟩ :=
    normalizedExteriorQuadraticFunctional_exists_relative_increment
  obtain ⟨reciprocalRadius, reciprocalPositive, reciprocalConstant, reciprocalOne, reciprocalBound⟩ :=
    normalizedC1Reciprocal_exists_uniform_bounds
  obtain ⟨identityRadius, identityPositive, identity⟩ :=
    normalizedExteriorQuadraticFunctional_exists_centered_identity
  let parameterRadius := min functionalRadius (min reciprocalRadius (min identityRadius (1 / 4)))
  refine ⟨radius, radiusPositive, parameterRadius, by dsimp only [parameterRadius]; positivity,
    functionalConstant * geometryConstant, mul_nonneg (by linarith) geometryNonnegative, ?_⟩
  intro initial final initialInside finalInside initialArea finalArea initialCentered finalCentered parameter small power
  have geometry := geometryBound initial final initialInside finalInside initialArea finalArea
  have functionalSmall : ‖parameter‖ ≤ functionalRadius := small.trans (min_le_left _ _)
  have reciprocalSmall : ‖parameter‖ ≤ reciprocalRadius :=
    small.trans ((min_le_right _ _).trans (min_le_left _ _))
  have identitySmall : ‖parameter‖ ≤ identityRadius :=
    small.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have parameterQuarter : ‖parameter‖ ≤ 1 / 4 :=
    small.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have reconstruction (state : PeriodicC1HolderHalf) :
      diskStationaryChart (diskRelabelNeutralCLM state) + diskPhysicalSpectralDefect state =
        diskPhysicalSpectralChart state := by unfold diskPhysicalSpectralDefect; abel
  have firstBaseNorm : ‖diskStationaryChart (diskRelabelNeutralCLM initial)‖ ≤ 3 := by
    linarith [geometry.2.2.1, norm_nonneg (diskPhysicalSpectralDefect initial), norm_nonneg (diskPhysicalSpectralDefect final)]
  have finalBaseNorm : ‖diskStationaryChart (diskRelabelNeutralCLM final)‖ ≤ 3 := by
    linarith [geometry.2.2.2.1, norm_nonneg (diskPhysicalSpectralDefect initial), norm_nonneg (diskPhysicalSpectralDefect final)]
  have firstPhysicalNorm : ‖diskPhysicalSpectralChart initial‖ ≤ 3 := by
    rw [← reconstruction initial]
    exact (norm_add_le _ _).trans (by linarith [geometry.2.2.1, norm_nonneg (diskPhysicalSpectralDefect final)])
  have finalPhysicalNorm : ‖diskPhysicalSpectralChart final‖ ≤ 3 := by
    rw [← reconstruction final]
    exact (norm_add_le _ _).trans (by linarith [geometry.2.2.2.1, norm_nonneg (diskPhysicalSpectralDefect initial)])
  have firstMoment : contourPolynomialMoment 1 (diskPhysicalSpectralChart initial) = 0 :=
    contourPolynomialMoment_one_eq_zero_of_centroid _ initialCentered (by
      change diskSpectralTubularArea initial ≠ 0
      rw [initialArea]
      exact Real.pi_ne_zero)
  have finalMoment : contourPolynomialMoment 1 (diskPhysicalSpectralChart final) = 0 :=
    contourPolynomialMoment_one_eq_zero_of_centroid _ finalCentered (by
      change diskSpectralTubularArea final ≠ 0
      rw [finalArea]
      exact Real.pi_ne_zero)
  have agreement (data : PeriodicC1HolderHalf) (bounded : ‖data‖ ≤ 3)
      (moment : contourPolynomialMoment 1 data = 0) :=
    identity parameter identitySmall power data (((reciprocalBound parameter reciprocalSmall).1 data bounded).1) moment
  have kernelContinuous : Continuous (fun label =>
      normalizedExteriorInversePowerKernel parameter power (standardCircle label)) := by
    have actual := normalizedExteriorInversePowerKernel_continuous_comp standardCircleBanach
      (by norm_num) 1 parameter (distance := 1 / 2) (by norm_num)
      (by rw [norm_one]; linarith) power
    simpa only [div_one] using actual
  have firstStationary := contourAntiholomorphicFunctional_stationary_base
    (normalizedExteriorInversePowerKernel parameter power) initial geometry.1 kernelContinuous
  have finalStationary := contourAntiholomorphicFunctional_stationary_base
    (normalizedExteriorInversePowerKernel parameter power) final geometry.2.1 kernelContinuous
  rw [← agreement _ firstBaseNorm (contourPolynomialMoment_stationary_base_positive initial geometry.1 0)] at firstStationary
  rw [← agreement _ finalBaseNorm (contourPolynomialMoment_stationary_base_positive final geometry.2.1 0)] at finalStationary
  have actual := functionalBound parameter functionalSmall power
    (diskStationaryChart (diskRelabelNeutralCLM initial)) (diskStationaryChart (diskRelabelNeutralCLM final))
    (diskPhysicalSpectralDefect initial) (diskPhysicalSpectralDefect final) geometry.2.2.1 geometry.2.2.2.1
  rw [reconstruction, reconstruction, firstStationary, finalStationary,
    sub_sub_sub_cancel_right, agreement _ firstPhysicalNorm firstMoment, agreement _ finalPhysicalNorm finalMoment] at actual
  exact actual.trans ((mul_le_mul_of_nonneg_left geometry.2.2.2.2 (by positivity)).trans_eq (by ring))

end EulerNonuniqueness.Paper
