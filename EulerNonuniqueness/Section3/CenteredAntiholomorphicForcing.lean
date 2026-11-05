import EulerNonuniqueness.Section3.RelabeledDiskForcingAnalytic
import EulerNonuniqueness.Section3.NormalizedShiftVelocity
import EulerNonuniqueness.Section3.ContourAnalyticMoments

namespace EulerNonuniqueness.Paper

noncomputable section

open MeasureTheory

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem contourPolynomialMoment_normalized_shift (degree : ℕ) (data : PeriodicC1HolderHalf) (offset : ℝ) :
    contourPolynomialMoment degree (normalizedContourShift offset data) =
      (standardCircle offset)⁻¹ ^ degree * contourPolynomialMoment degree data := by
  let rotation := (standardCircle offset)⁻¹
  have unit : rotation * star rotation = (1 : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp [rotation, norm_inv, standardCircle_norm]
  let integrand := fun source => data.val.1 source ^ degree * star (data.val.1 source) * data.val.2.val.1 source
  have periodic : Function.Periodic integrand (2 * Real.pi) := by
    intro source
    dsimp only [integrand]
    rw [PeriodicC1HolderHalf.periodic data source, PeriodicHolderHalf.periodic data.val.2 source]
  have window := periodic.intervalIntegral_add_eq (-Real.pi) (-Real.pi + offset)
  have firstEndpoint : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have secondEndpoint : -Real.pi + offset + 2 * Real.pi = Real.pi + offset := by ring
  rw [firstEndpoint, secondEndpoint] at window
  rw [contourPolynomialMoment_eq_integral, contourPolynomialMoment_eq_integral]
  have integrandEquality : (fun label => ((normalizedContourShift offset data).val.1 label) ^ degree *
      star ((normalizedContourShift offset data).val.1 label) * (normalizedContourShift offset data).val.2.val.1 label) =
      fun label => rotation ^ degree * integrand (label + offset) := by
    funext label
    simp only [normalizedContourShift_value, normalizedContourShift_tangent,
      mul_pow, star_mul]
    change (rotation ^ degree * data.val.1 (label + offset) ^ degree) *
      (star (data.val.1 (label + offset)) * star rotation) *
      (rotation * data.val.2.val.1 (label + offset)) = _
    calc
      _ = (rotation * star rotation) * (rotation ^ degree * integrand (label + offset)) := by dsimp only [integrand]; ring
      _ = _ := by rw [unit, one_mul]
  rw [integrandEquality, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right, ← window]
  dsimp only [rotation, integrand]
  ring

def centeredAntiholomorphicForcing (degree : ℕ) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  c1Conjugate (c1NaturalPower data (degree + 1)) -
    c1Constant (star (contourPolynomialMoment (degree + 1) data) / (Real.pi : ℂ))

theorem centeredAntiholomorphicForcing_value (degree : ℕ) (data : PeriodicC1HolderHalf) (label : ℝ) :
    (centeredAntiholomorphicForcing degree data).val.1 label =
      star (data.val.1 label) ^ (degree + 1) - star (contourPolynomialMoment (degree + 1) data) / (Real.pi : ℂ) := by
  change star ((c1NaturalPower data (degree + 1)).val.1 label) - _ = _
  rw [c1NaturalPower_value, star_pow, c1Constant_value]

theorem centeredAntiholomorphicForcing_normalized_shift (degree : ℕ) (data : PeriodicC1HolderHalf) (offset : ℝ) :
    normalizedContourShift offset (centeredAntiholomorphicForcing degree data) =
      ((standardCircle offset)⁻¹ ^ (degree + 2)) •
        centeredAntiholomorphicForcing degree (normalizedContourShift offset data) := by
  let rotation := (standardCircle offset)⁻¹
  have unit : rotation * star rotation = (1 : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp [rotation, norm_inv, standardCircle_norm]
  have cancellation : rotation ^ (degree + 1) * star rotation ^ (degree + 1) = (1 : ℂ) := by
    rw [← mul_pow, unit, one_pow]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [normalizedContourShift_value, centeredAntiholomorphicForcing_value, complexC1Holder_smul_value,
    centeredAntiholomorphicForcing_value, normalizedContourShift_value, contourPolynomialMoment_normalized_shift]
  simp only [star_mul, star_pow]
  change rotation * (star (data.val.1 (label + offset)) ^ (degree + 1) -
      star (contourPolynomialMoment (degree + 1) data) / (Real.pi : ℂ)) =
    rotation ^ (degree + 2) * ((star (data.val.1 (label + offset)) * star rotation) ^ (degree + 1) -
      (star (contourPolynomialMoment (degree + 1) data) * star rotation ^ (degree + 1)) / (Real.pi : ℂ))
  rw [show degree + 2 = (degree + 1) + 1 by omega, pow_succ, mul_pow]
  calc
    _ = (rotation ^ (degree + 1) * star rotation ^ (degree + 1)) *
        (rotation * (star (data.val.1 (label + offset)) ^ (degree + 1) -
          star (contourPolynomialMoment (degree + 1) data) / (Real.pi : ℂ))) := by rw [cancellation, one_mul]; ring
    _ = _ := by ring

end

end EulerNonuniqueness.Paper
