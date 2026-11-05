import EulerNonuniqueness.Section3.ContourMomentSpectralAbsolute
import EulerNonuniqueness.Section3.ExteriorGeneralContourSeries
import EulerNonuniqueness.Section3.ContourPolynomialCentroidGauge
import EulerNonuniqueness.Section3.ExteriorSeriesLeadingMode
import EulerNonuniqueness.General.WeightedScalarProductSeries

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

def contourExteriorCentroidResponse (phase : Circle) (coefficients : ℕ → ℂ) (data : PeriodicC1HolderHalf) : ℂ :=
  ∑' power : ℕ, ((phase : ℂ)⁻¹ ^ (power + 2) * coefficients power) *
    (star (contourPolynomialMoment (power + 1) data) / (Real.pi : ℂ))

theorem contourExteriorCentroidResponse_eq_centroid_derivative
    (phase : Circle) (coefficients : ℕ → ℂ) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) (bounded : ‖data‖ ≤ 3)
    (area : contourAreaFunctional data = Real.pi)
    (summable : Summable (fun power => (24 : ℝ) ^ (power + 1) * ‖coefficients power‖)) :
    contourExteriorCentroidResponse phase coefficients data =
      fderiv ℝ contourCentroidFunctional data
        (∑' power, rotatedExteriorPower phase data power (coefficients power)) := by
  have actual := (fderiv ℝ contourCentroidFunctional data).hasSum
    (rotatedExteriorPower_summable phase data bounded coefficients summable).hasSum
  have term (power : ℕ) : fderiv ℝ contourCentroidFunctional data
      (rotatedExteriorPower phase data power (coefficients power)) =
      ((phase : ℂ)⁻¹ ^ (power + 2) * coefficients power) *
        (star (contourPolynomialMoment (power + 1) data) / (Real.pi : ℂ)) := by
    unfold rotatedExteriorPower
    rw [contourCentroidFunctional_derivative_complexPolynomial data (power + 1) _ small, area]
  simp only [term] at actual
  exact actual.tsum_eq

theorem contourExteriorCentroidResponse_exists_spectral_relative_ball :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ initial final : PeriodicC1HolderHalf, initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      ∀ phase : Circle, ∀ firstCoefficients secondCoefficients : ℕ → ℂ,
      Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖firstCoefficients power‖) →
      Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖secondCoefficients power‖) →
      Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖firstCoefficients power - secondCoefficients power‖) →
      ‖contourExteriorCentroidResponse phase firstCoefficients (diskPhysicalSpectralChart initial) -
        contourExteriorCentroidResponse phase secondCoefficients (diskPhysicalSpectralChart final)‖ ≤
      constant * ((∑' power, (96 : ℝ) ^ (power + 1) * ‖firstCoefficients power‖) *
          (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
            (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
              ‖diskNeutralCLM initial - diskNeutralCLM final‖) +
        (∑' power, (96 : ℝ) ^ (power + 1) * ‖firstCoefficients power - secondCoefficients power‖) *
          ‖diskPhysicalTransverseProjection final‖) := by
  obtain ⟨relativeRadius, relativePositive, relativeConstant, relativeNonnegative, relativeBound⟩ :=
    contourPolynomialMoment_exists_spectral_relative_ball
  obtain ⟨absoluteRadius, absolutePositive, absoluteConstant, absoluteNonnegative, absoluteBound⟩ :=
    contourPolynomialMoment_exists_spectral_absolute_ball
  let constant := (relativeConstant + absoluteConstant + 1) / Real.pi
  have constantNonnegative : 0 ≤ constant := by dsimp only [constant]; positivity
  have relativeScalar : relativeConstant / Real.pi ≤ constant := by dsimp only [constant]; gcongr; linarith
  have absoluteScalar : absoluteConstant / Real.pi ≤ constant := by dsimp only [constant]; gcongr; linarith
  refine ⟨min relativeRadius absoluteRadius, by positivity, constant, constantNonnegative, ?_⟩
  intro initial final initialInside finalInside initialArea finalArea phase firstCoefficients secondCoefficients
    firstSummable secondSummable differenceSummable
  let firstRotated := fun power : ℕ => (phase : ℂ)⁻¹ ^ (power + 2) * firstCoefficients power
  let secondRotated := fun power : ℕ => (phase : ℂ)⁻¹ ^ (power + 2) * secondCoefficients power
  let firstVectors := fun power : ℕ => star (contourPolynomialMoment (power + 1) (diskPhysicalSpectralChart initial)) / (Real.pi : ℂ)
  let secondVectors := fun power : ℕ => star (contourPolynomialMoment (power + 1) (diskPhysicalSpectralChart final)) / (Real.pi : ℂ)
  let budget := ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
    (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
      ‖diskNeutralCLM initial - diskNeutralCLM final‖
  have firstNorm (power : ℕ) : ‖firstRotated power‖ = ‖firstCoefficients power‖ := by
    simp only [firstRotated, norm_mul, norm_pow, norm_inv, Circle.norm_coe, inv_one, one_pow, one_mul]
  have secondNorm (power : ℕ) : ‖secondRotated power‖ = ‖secondCoefficients power‖ := by
    simp only [secondRotated, norm_mul, norm_pow, norm_inv, Circle.norm_coe, inv_one, one_pow, one_mul]
  have differenceNorm (power : ℕ) : ‖firstRotated power - secondRotated power‖ =
      ‖firstCoefficients power - secondCoefficients power‖ := by
    dsimp only [firstRotated, secondRotated]
    rw [← mul_sub]
    simp only [norm_mul, norm_pow, norm_inv, Circle.norm_coe, inv_one, one_pow, one_mul]
  have vectorsDifference (power : ℕ) : ‖firstVectors power - secondVectors power‖ ≤
      constant * (96 : ℝ) ^ (power + 1) * budget := by
    dsimp only [firstVectors, secondVectors]
    rw [← sub_div, ← star_sub, norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have estimate := div_le_div_of_nonneg_right
      (relativeBound initial final (ball_subset_ball (min_le_left _ _) initialInside)
        (ball_subset_ball (min_le_left _ _) finalInside) initialArea finalArea power) Real.pi_pos.le
    apply estimate.trans
    convert mul_le_mul_of_nonneg_right relativeScalar
      (show 0 ≤ (96 : ℝ) ^ (power + 1) * budget by dsimp only [budget]; positivity) using 1 <;> ring
  have finalVector (power : ℕ) : ‖secondVectors power‖ ≤
      constant * (96 : ℝ) ^ (power + 1) * ‖diskPhysicalTransverseProjection final‖ := by
    dsimp only [secondVectors]
    rw [norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have estimate := div_le_div_of_nonneg_right
      (absoluteBound final (ball_subset_ball (min_le_right _ _) finalInside) finalArea power) Real.pi_pos.le
    apply estimate.trans
    convert mul_le_mul_of_nonneg_right absoluteScalar
      (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 96) (power + 1))
        (norm_nonneg (diskPhysicalTransverseProjection final))) using 1 <;> ring
  have actual := EulerNonuniqueness.General.norm_tsum_smul_sub_tsum_smul_le_weighted
    firstRotated secondRotated firstVectors secondVectors (fun power => (96 : ℝ) ^ (power + 1))
    (by simpa only [firstNorm] using firstSummable) (by simpa only [secondNorm] using secondSummable)
    (by simpa only [differenceNorm] using differenceSummable) vectorsDifference finalVector
  simpa only [contourExteriorCentroidResponse, firstRotated, secondRotated, firstVectors, secondVectors,
    smul_eq_mul, firstNorm, differenceNorm, budget] using actual.2.2

theorem contourExteriorCentroidResponse_without_leading
    (phase : Circle) (coefficients : ℕ → ℂ) (data : PeriodicC1HolderHalf)
    (centered : contourCentroidFunctional data = 0) (areaNonzero : contourAreaFunctional data ≠ 0) :
    contourExteriorCentroidResponse phase coefficients data =
      contourExteriorCentroidResponse phase (exteriorCoefficientWithoutLeading coefficients) data := by
  unfold contourExteriorCentroidResponse
  apply tsum_congr
  intro power
  by_cases zero : power = 0
  · subst power
    have momentZero : contourPolynomialMoment 1 data = 0 := by
      change contourPolynomialMoment 1 data / (contourAreaFunctional data : ℂ) = 0 at centered
      exact (div_eq_zero_iff.mp centered).resolve_right (Complex.ofReal_ne_zero.mpr areaNonzero)
    simp only [exteriorCoefficientWithoutLeading, ite_true, mul_zero, zero_mul, Nat.zero_add,
      momentZero, star_zero, zero_div, mul_zero]
  · simp only [exteriorCoefficientWithoutLeading, if_neg zero]

end EulerNonuniqueness.Paper
