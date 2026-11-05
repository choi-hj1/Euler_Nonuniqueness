import EulerNonuniqueness.Section3.NormalizedExteriorQuadraticFunctional
import EulerNonuniqueness.Section3.ContourAnalyticCentroid

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  c1InverseAnalyticOperatorGroup c1InverseAnalyticOperatorSpace
  antiholomorphicPairOperatorGroup antiholomorphicPairOperatorSpace
  functionalUniformBilinearGroup functionalUniformBilinearSpace
  functionalUniformThirdGroup functionalUniformThirdSeminormedGroup
  functionalUniformThirdSeminormedAddGroup functionalUniformThirdSpace

theorem contourAntiholomorphicFunctional_conjugate (data : PeriodicC1HolderHalf) :
    contourAntiholomorphicFunctional (fun position : ℂ => star position) data =
      star (contourPolynomialMoment 1 data) := by
  simpa only [contourAntiholomorphicFunctional, pow_one] using
    (contourPolynomialMoment_conjugate_integral data 1).symm

theorem contourPolynomialMoment_one_eq_zero_of_centroid (data : PeriodicC1HolderHalf)
    (centered : contourCentroidFunctional data = 0)
    (areaNonzero : contourAreaFunctional data ≠ 0) : contourPolynomialMoment 1 data = 0 := by
  have denominator : (contourAreaFunctional data : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr areaNonzero
  exact (div_eq_zero_iff.mp centered).resolve_right denominator

theorem normalizedExteriorQuadraticFunctional_exists_centered_identity :
    ∃ parameterRadius > (0 : ℝ), ∀ parameter : ℂ, ‖parameter‖ ≤ parameterRadius → ∀ power : ℕ,
      ∀ data : PeriodicC1HolderHalf,
      ‖normalizedC1Denominator parameter data - c1Constant 1‖ ≤ 1 / 2 →
      contourPolynomialMoment 1 data = 0 →
      normalizedExteriorQuadraticFunctional parameter power data =
        contourAntiholomorphicFunctional (normalizedExteriorInversePowerKernel parameter power) data := by
  obtain ⟨parameterRadius, positive, zeroJet⟩ := normalizedExteriorKernelC1_exists_derivative_zero
  refine ⟨parameterRadius, positive, ?_⟩
  intro parameter small power data denominator moment
  have linearIdentity := contourAntiholomorphicFunctional_eq_pair
    (fun position : ℂ => (power + 1 : ℂ) * star parameter * star position) data
    (normalizedExteriorKernelC1Derivative parameter power 0 data)
    (zeroJet parameter small power data)
  rw [contourAntiholomorphicFunctional_mul_const, contourAntiholomorphicFunctional_conjugate,
    moment] at linearIdentity
  simp only [star_zero, mul_zero] at linearIdentity
  have expansion : normalizedExteriorQuadraticFunctional parameter power data =
      normalizedExteriorFunctional parameter power data -
        contourAntiholomorphicTripleCLM data (normalizedExteriorKernelC1Derivative parameter power 0 data) data := by
    unfold normalizedExteriorQuadraticFunctional normalizedExteriorFunctional normalizedExteriorQuadraticKernelC1
    simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [expansion, contourAntiholomorphicTripleCLM_apply, ← linearIdentity, sub_zero]
  exact normalizedExteriorFunctional_eq_contour parameter power data denominator

end EulerNonuniqueness.Paper
