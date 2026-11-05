import EulerNonuniqueness.Section3.PeriodicHilbertSpectral

open MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] projectionHolderRealSpace projectionC1RealSpace projectionC1Module
  projectionC1ComplexSpace projectionC1BoundedSMul projectionC1ContinuousAdd projectionC1UniformAdd

local instance projectionFourierPositivePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def periodicC1FourierCoefficient (data : PeriodicC1HolderHalf) (degree : ℤ) : ℂ :=
  fourierCoeff (periodicContinuousLift data.val.1.continuous (PeriodicC1HolderHalf.periodic data)) degree

theorem periodicC1FourierCoefficient_interval (data : PeriodicC1HolderHalf) (degree : ℤ) :
    periodicC1FourierCoefficient data degree = (1 / (2 * Real.pi) : ℝ) •
      ∫ label in (0 : ℝ)..(2 * Real.pi), circleFourierReal (-degree) label * data.val.1 label := by
  unfold periodicC1FourierCoefficient
  rw [fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add, periodicContinuousLift_coe, smul_eq_mul]
  rfl

theorem periodicC1FourierCoefficient_add (first second : PeriodicC1HolderHalf) (degree : ℤ) :
    periodicC1FourierCoefficient (first + second) degree =
      periodicC1FourierCoefficient first degree + periodicC1FourierCoefficient second degree := by
  rw [periodicC1FourierCoefficient_interval, periodicC1FourierCoefficient_interval,
    periodicC1FourierCoefficient_interval]
  change (1 / (2 * Real.pi) : ℝ) •
    (∫ label in (0 : ℝ)..(2 * Real.pi), circleFourierReal (-degree) label * (first.val.1 label + second.val.1 label)) = _
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add
    (((circleFourierReal_continuous (-degree)).mul first.val.1.continuous).intervalIntegrable _ _)
    (((circleFourierReal_continuous (-degree)).mul second.val.1.continuous).intervalIntegrable _ _), smul_add]

theorem periodicC1FourierCoefficient_smul (scalar : ℂ) (data : PeriodicC1HolderHalf) (degree : ℤ) :
    periodicC1FourierCoefficient (scalar • data) degree = scalar * periodicC1FourierCoefficient data degree := by
  rw [periodicC1FourierCoefficient_interval, periodicC1FourierCoefficient_interval]
  simp_rw [complexC1Holder_smul_value]
  have integrand : (fun label => circleFourierReal (-degree) label * (scalar * data.val.1 label)) =
      (fun label => scalar * (circleFourierReal (-degree) label * data.val.1 label)) := by
    funext label
    ring
  rw [integrand, intervalIntegral.integral_const_mul]
  simp only [Complex.real_smul]
  ring

theorem periodicC1FourierCoefficient_zero (degree : ℤ) :
    periodicC1FourierCoefficient (0 : PeriodicC1HolderHalf) degree = 0 := by
  rw [periodicC1FourierCoefficient_interval]
  change (1 / (2 * Real.pi) : ℝ) • (∫ label in (0 : ℝ)..(2 * Real.pi), circleFourierReal (-degree) label * 0) = 0
  simp

theorem periodicC1FourierCoefficient_hilbert (data : PeriodicC1HolderHalf) (degree : ℤ) :
    periodicC1FourierCoefficient (periodicHilbertC1 data) degree =
      periodicHilbertMultiplier degree * periodicC1FourierCoefficient data degree :=
  periodicHilbertC1_fourierCoeff data degree

theorem periodicHilbertMultiplier_ne_zero {degree : ℤ} (nonzero : degree ≠ 0) :
    periodicHilbertMultiplier degree ≠ 0 := by
  cases degree with
  | ofNat index =>
      cases index with
      | zero => exact False.elim (nonzero rfl)
      | succ index => exact neg_ne_zero.mpr Complex.I_ne_zero
  | negSucc index => exact Complex.I_ne_zero

theorem periodicC1FourierCoefficient_meanZeroPart (data : PeriodicC1HolderHalf) {degree : ℤ}
    (nonzero : degree ≠ 0) :
    periodicC1FourierCoefficient (periodicMeanZeroPartCCLM data) degree = periodicC1FourierCoefficient data degree := by
  have identity := congrArg (fun value : PeriodicC1HolderHalf => periodicC1FourierCoefficient value degree)
    (periodicHilbertC1_meanZeroPart data)
  dsimp only at identity
  rw [periodicC1FourierCoefficient_hilbert, periodicC1FourierCoefficient_hilbert] at identity
  exact mul_left_cancel₀ (periodicHilbertMultiplier_ne_zero nonzero) identity

theorem periodicHilbertPositiveProjection_fourier_nonpositive_zero
    (data : PeriodicC1HolderHalf) (degree : ℤ) (nonpositive : degree ≤ 0) :
    periodicC1FourierCoefficient (periodicHilbertPositiveProjection data) degree = 0 := by
  have identity := congrArg (fun value : PeriodicC1HolderHalf => periodicC1FourierCoefficient value degree)
    (periodicHilbertC1_positiveProjection data)
  dsimp only at identity
  rw [periodicC1FourierCoefficient_hilbert, periodicC1FourierCoefficient_smul] at identity
  cases degree with
  | ofNat index =>
      change (index : ℤ) ≤ 0 at nonpositive
      have zero : index = 0 := by omega
      subst index
      simp only [periodicHilbertMultiplier, zero_mul] at identity
      exact (mul_eq_zero.mp identity.symm).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
  | negSucc index =>
      simp only [periodicHilbertMultiplier] at identity
      have annihilated : (2 * Complex.I) *
          periodicC1FourierCoefficient (periodicHilbertPositiveProjection data) (Int.negSucc index) = 0 := by
        linear_combination identity
      exact (mul_eq_zero.mp annihilated).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)

theorem periodicHilbertNegativeProjection_fourier_nonnegative_zero
    (data : PeriodicC1HolderHalf) (degree : ℤ) (nonnegative : 0 ≤ degree) :
    periodicC1FourierCoefficient (periodicHilbertNegativeProjection data) degree = 0 := by
  have identity := congrArg (fun value : PeriodicC1HolderHalf => periodicC1FourierCoefficient value degree)
    (periodicHilbertC1_negativeProjection data)
  dsimp only at identity
  rw [periodicC1FourierCoefficient_hilbert, periodicC1FourierCoefficient_smul] at identity
  cases degree with
  | ofNat index =>
      cases index with
      | zero =>
          simp only [periodicHilbertMultiplier, zero_mul] at identity
          exact (mul_eq_zero.mp identity.symm).resolve_left Complex.I_ne_zero
      | succ index =>
          simp only [periodicHilbertMultiplier] at identity
          have annihilated : (2 * Complex.I) *
              periodicC1FourierCoefficient (periodicHilbertNegativeProjection data) (Int.ofNat (index + 1)) = 0 := by
            linear_combination -identity
          exact (mul_eq_zero.mp annihilated).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  | negSucc index => omega

theorem periodicHilbertPositiveProjection_fourier_positive_eq
    (data : PeriodicC1HolderHalf) (degree : ℤ) (positive : 0 < degree) :
    periodicC1FourierCoefficient (periodicHilbertPositiveProjection data) degree =
      periodicC1FourierCoefficient data degree := by
  have identity := congrArg (fun value : PeriodicC1HolderHalf => periodicC1FourierCoefficient value degree)
    (periodicHilbertProjections_sum data)
  dsimp only at identity
  rw [periodicC1FourierCoefficient_add,
    periodicC1FourierCoefficient_meanZeroPart data (ne_of_gt positive),
    periodicHilbertNegativeProjection_fourier_nonnegative_zero data degree positive.le, add_zero] at identity
  exact identity

theorem periodicHilbertNegativeProjection_fourier_negative_eq
    (data : PeriodicC1HolderHalf) (degree : ℤ) (negative : degree < 0) :
    periodicC1FourierCoefficient (periodicHilbertNegativeProjection data) degree =
      periodicC1FourierCoefficient data degree := by
  have identity := congrArg (fun value : PeriodicC1HolderHalf => periodicC1FourierCoefficient value degree)
    (periodicHilbertProjections_sum data)
  dsimp only at identity
  rw [periodicC1FourierCoefficient_add,
    periodicC1FourierCoefficient_meanZeroPart data (ne_of_lt negative),
    periodicHilbertPositiveProjection_fourier_nonpositive_zero data degree negative.le, zero_add] at identity
  exact identity

theorem periodicHilbertPositiveProjection_fourier_one (data : PeriodicC1HolderHalf) :
    periodicC1FourierCoefficient (periodicHilbertPositiveProjection data) 1 = periodicC1FourierCoefficient data 1 :=
  periodicHilbertPositiveProjection_fourier_positive_eq data 1 (by norm_num)

theorem periodicHilbertNegativeProjection_eq_zero_of_negative_coefficients
    (data : PeriodicC1HolderHalf)
    (coefficients : ∀ degree : ℤ, degree < 0 → periodicC1FourierCoefficient data degree = 0) :
    periodicHilbertNegativeProjection data = 0 := by
  have functionEquality := eq_of_periodic_fourierCoeff_eq
    (periodicHilbertNegativeProjection data).val.1.continuous (0 : PeriodicC1HolderHalf).val.1.continuous
    (PeriodicC1HolderHalf.periodic _) (PeriodicC1HolderHalf.periodic _) (fun degree => by
      change periodicC1FourierCoefficient (periodicHilbertNegativeProjection data) degree =
        periodicC1FourierCoefficient (0 : PeriodicC1HolderHalf) degree
      rw [periodicC1FourierCoefficient_zero]
      by_cases negative : degree < 0
      · rw [periodicHilbertNegativeProjection_fourier_negative_eq data degree negative]
        exact coefficients degree negative
      · exact periodicHilbertNegativeProjection_fourier_nonnegative_zero data degree (le_of_not_gt negative))
  exact PeriodicC1HolderHalf.ext_value (fun label => congrFun functionEquality label)

theorem periodicHilbertPositiveProjection_eq_zero_of_positive_coefficients
    (data : PeriodicC1HolderHalf)
    (coefficients : ∀ degree : ℤ, 0 < degree → periodicC1FourierCoefficient data degree = 0) :
    periodicHilbertPositiveProjection data = 0 := by
  have functionEquality := eq_of_periodic_fourierCoeff_eq
    (periodicHilbertPositiveProjection data).val.1.continuous (0 : PeriodicC1HolderHalf).val.1.continuous
    (PeriodicC1HolderHalf.periodic _) (PeriodicC1HolderHalf.periodic _) (fun degree => by
      change periodicC1FourierCoefficient (periodicHilbertPositiveProjection data) degree =
        periodicC1FourierCoefficient (0 : PeriodicC1HolderHalf) degree
      rw [periodicC1FourierCoefficient_zero]
      by_cases positive : 0 < degree
      · rw [periodicHilbertPositiveProjection_fourier_positive_eq data degree positive]
        exact coefficients degree positive
      · exact periodicHilbertPositiveProjection_fourier_nonpositive_zero data degree (le_of_not_gt positive))
  exact PeriodicC1HolderHalf.ext_value (fun label => congrFun functionEquality label)

end

end EulerNonuniqueness.Paper
