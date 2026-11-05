import EulerNonuniqueness.Section3.DiskPhysicalGenerator
import EulerNonuniqueness.Section3.PeriodicHilbertModes

namespace EulerNonuniqueness.Paper

noncomputable section

open MeasureTheory

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance forcingModeHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance forcingModeC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance forcingModeHolderComplexModule : Module ℂ PeriodicHolderHalf := Submodule.module complexPeriodicHolderGraph
local instance forcingModeC1ComplexModule : Module ℂ PeriodicC1HolderHalf := Submodule.module complexPeriodicC1HolderGraph
local instance forcingModeHolderComplexSpace : NormedSpace ℂ PeriodicHolderHalf := complexHolderNormedSpace
local instance forcingModeC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf := complexC1HolderNormedSpace

def diskCircleMode : ℕ → PeriodicC1HolderHalf
  | 0 => c1Constant 1
  | degree + 1 => c1Product standardCircleBanach (diskCircleMode degree)

theorem diskCircleMode_value (degree : ℕ) (label : ℝ) :
    (diskCircleMode degree).val.1 label = standardCircle label ^ degree := by
  induction degree with
  | zero => rfl
  | succ degree induction =>
    change standardCircle label * (diskCircleMode degree).val.1 label = _
    rw [induction, pow_succ]
    ring

theorem diskCircleMode_holder (degree : ℕ) :
    c1ValueHolder (diskCircleMode degree) = positiveCircleMode degree := by
  apply PeriodicHolderHalf.ext_value
  intro label
  exact (diskCircleMode_value degree label).trans (positiveCircleMode_value degree label).symm

theorem diskCircleMode_hilbert (degree : ℕ) :
    periodicHilbertC1 (diskCircleMode (degree + 1)) = -Complex.I • diskCircleMode (degree + 1) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [periodicHilbertC1_value, diskCircleMode_holder, periodicHilbertCLM_positive_mode]
  change -Complex.I * (positiveCircleMode (degree + 1)).val.1 label =
    -Complex.I * (diskCircleMode (degree + 1)).val.1 label
  rw [positiveCircleMode_value, diskCircleMode_value]

theorem diskCircleMode_conjugate_hilbert (degree : ℕ) :
    periodicHilbertC1 (c1Conjugate (diskCircleMode (degree + 1))) =
      Complex.I • c1Conjugate (diskCircleMode (degree + 1)) := by
  have embedding : c1ValueHolder (c1Conjugate (diskCircleMode (degree + 1))) =
      holderConjugate (positiveCircleMode (degree + 1)) := by
    apply PeriodicHolderHalf.ext_value
    intro label
    change star ((diskCircleMode (degree + 1)).val.1 label) =
      star ((positiveCircleMode (degree + 1)).val.1 label)
    rw [positiveCircleMode_value, diskCircleMode_value]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [periodicHilbertC1_value, embedding, periodicHilbertCLM_negative_mode]
  change Complex.I * star ((positiveCircleMode (degree + 1)).val.1 label) =
    Complex.I * star ((diskCircleMode (degree + 1)).val.1 label)
  rw [positiveCircleMode_value, diskCircleMode_value]

theorem diskCircleMode_integral (degree : ℕ) :
    c1AngularIntegralCCLM (diskCircleMode (degree + 1)) = 0 := by
  change (∫ label in (0 : ℝ)..(2 * Real.pi), (diskCircleMode (degree + 1)).val.1 label) = 0
  have window := (PeriodicC1HolderHalf.periodic (diskCircleMode (degree + 1))).intervalIntegral_add_eq (-Real.pi) 0
  have endpoint : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [endpoint, zero_add] at window
  rw [← window]
  simp_rw [diskCircleMode_value]
  exact integral_standardCircle_pow_succ degree

theorem diskCircleMode_conjugate_integral (degree : ℕ) :
    c1AngularIntegralCCLM (c1Conjugate (diskCircleMode (degree + 1))) = 0 := by
  change (∫ label in (0 : ℝ)..(2 * Real.pi), star ((diskCircleMode (degree + 1)).val.1 label)) = 0
  have identity : (∫ label in (0 : ℝ)..(2 * Real.pi), star ((diskCircleMode (degree + 1)).val.1 label)) =
      star (∫ label in (0 : ℝ)..(2 * Real.pi), (diskCircleMode (degree + 1)).val.1 label) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm
      ((diskCircleMode (degree + 1)).val.1.continuous.intervalIntegrable (μ := volume) (0 : ℝ) (2 * Real.pi))
  rw [identity]
  change star (c1AngularIntegralCCLM (diskCircleMode (degree + 1))) = 0
  rw [diskCircleMode_integral, star_zero]

theorem diskForcingMode_radial (degree : ℕ) (coefficient : ℂ) :
    diskRadialPart (coefficient • c1Conjugate (diskCircleMode (degree + 1))) =
      (1 / 2 : ℂ) • (coefficient • c1Conjugate (diskCircleMode (degree + 2)) +
        star coefficient • diskCircleMode (degree + 2)) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  have addValue (first second : PeriodicC1HolderHalf) :
      (first + second).val.1 label = first.val.1 label + second.val.1 label := rfl
  change (1 / 2 : ℝ) •
    (star (standardCircle label) * (coefficient * star ((diskCircleMode (degree + 1)).val.1 label)) +
      star (star (standardCircle label) * (coefficient * star ((diskCircleMode (degree + 1)).val.1 label)))) = _
  simp only [diskCircleMode_value, Complex.real_smul, star_mul, star_star, star_pow,
    complexC1Holder_smul_value, addValue, c1Conjugate_value, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  change (1 / 2 : ℂ) *
    (star (standardCircle label) * (coefficient * star (standardCircle label) ^ (degree + 1)) +
        standardCircle label ^ (degree + 1) * star coefficient * standardCircle label) =
    (1 / 2 : ℂ) * (coefficient * star (standardCircle label) ^ (degree + 2) +
      star coefficient * standardCircle label ^ (degree + 2))
  simp only [show degree + 2 = (degree + 1) + 1 by omega, pow_succ]
  ring

theorem diskForcingMode_radial_hilbert (degree : ℕ) (coefficient : ℂ) :
    periodicHilbertC1 (diskRadialPart (coefficient • c1Conjugate (diskCircleMode (degree + 1)))) =
      (1 / 2 : ℂ) • (coefficient • (Complex.I • c1Conjugate (diskCircleMode (degree + 2))) +
        star coefficient • (-Complex.I • diskCircleMode (degree + 2))) := by
  rw [diskForcingMode_radial, periodicHilbertC1_smul_complex, periodicHilbertC1_add,
    periodicHilbertC1_smul_complex, periodicHilbertC1_smul_complex,
    show degree + 2 = (degree + 1) + 1 by omega,
    diskCircleMode_conjugate_hilbert, diskCircleMode_hilbert]

theorem diskForcingMode_radial_integral (degree : ℕ) (coefficient : ℂ) :
    c1AngularIntegralCCLM (diskRadialPart (coefficient • c1Conjugate (diskCircleMode (degree + 1)))) = 0 := by
  rw [diskForcingMode_radial, map_smul, map_add, map_smul, map_smul,
    show degree + 2 = (degree + 1) + 1 by omega,
    diskCircleMode_integral, diskCircleMode_conjugate_integral]
  simp

theorem diskForcingMode_radial_mean (degree : ℕ) (coefficient : ℂ) :
    periodicMeanProjectionCCLM
      (diskRadialPart (coefficient • c1Conjugate (diskCircleMode (degree + 1)))) = 0 := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [periodicMeanProjectionCCLM_value]
  change (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
    c1AngularIntegralCCLM (diskRadialPart (coefficient • c1Conjugate (diskCircleMode (degree + 1)))) = 0
  rw [diskForcingMode_radial_integral, mul_zero]

theorem diskRotatingDerivative_forcing_mode (degree : ℕ) (coefficient : ℂ) :
    diskRotatingDerivative (coefficient • c1Conjugate (diskCircleMode (degree + 1))) =
      (-Complex.I / 2 * coefficient) • c1Conjugate (diskCircleMode (degree + 1)) := by
  rw [diskRotatingDerivative_apply, disk_contour_generator,
    diskForcingMode_radial_hilbert, diskForcingMode_radial_mean, diskForcingMode_radial]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change standardCircle label *
    (-(1 / 2 : ℝ) • ((1 / 2 : ℂ) *
      (coefficient * (Complex.I * star ((diskCircleMode (degree + 2)).val.1 label)) +
        star coefficient * (-Complex.I * (diskCircleMode (degree + 2)).val.1 label))) -
      (Complex.I / 2) * ((1 / 2 : ℂ) *
        (coefficient * star ((diskCircleMode (degree + 2)).val.1 label) +
          star coefficient * (diskCircleMode (degree + 2)).val.1 label) - 0)) =
    (-Complex.I / 2 * coefficient) * star ((diskCircleMode (degree + 1)).val.1 label)
  simp only [diskCircleMode_value, Complex.real_smul, star_pow]
  push_cast
  have circleNonzero : standardCircle label ≠ 0 := by
    intro zero
    have positive := standardCircle_norm label
    rw [zero, norm_zero] at positive
    norm_num at positive
  rw [standardCircle_star_eq_inv]
  have cancellation : standardCircle label * (standardCircle label)⁻¹ ^ (degree + 2) =
      (standardCircle label)⁻¹ ^ (degree + 1) := by
    rw [show degree + 2 = (degree + 1) + 1 by omega, pow_succ]
    calc
      _ = (standardCircle label * (standardCircle label)⁻¹) *
          (standardCircle label)⁻¹ ^ (degree + 1) := by ring
      _ = _ := by rw [mul_inv_cancel₀ circleNonzero, one_mul]
  calc
    _ = (-Complex.I / 2 * coefficient) *
        (standardCircle label * (standardCircle label)⁻¹ ^ (degree + 2)) := by ring
    _ = _ := by rw [cancellation]

end

end EulerNonuniqueness.Paper
