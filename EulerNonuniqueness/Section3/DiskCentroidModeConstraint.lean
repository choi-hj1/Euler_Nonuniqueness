import EulerNonuniqueness.Section3.DiskAreaMeanConstraint
import EulerNonuniqueness.Section3.ContourAnalyticCentroid

namespace EulerNonuniqueness.Paper

open MeasureTheory

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance centroidModeHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance centroidModeC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

def diskRadialFirstMode (direction : PeriodicC1HolderHalf) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) • ∫ label in (-Real.pi)..Real.pi,
    standardCircle label * ((star (standardCircle label) * direction.val.1 label).re : ℂ)

theorem integral_contourTangent_period_zero (data : PeriodicC1HolderHalf) :
    (∫ label in (-Real.pi)..Real.pi, data.val.2.val.1 label) = 0 := by
  have actual := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun label _ => PeriodicC1HolderHalf.hasDerivAt data label)
    (data.val.2.val.1.continuous.intervalIntegrable (-Real.pi) Real.pi)
  have endpoint : data.val.1 Real.pi = data.val.1 (-Real.pi) := by
    simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using
      PeriodicC1HolderHalf.periodic data (-Real.pi)
  simpa only [endpoint, sub_self] using actual

theorem disk_first_moment_integrand_expansion (direction : PeriodicC1HolderHalf) (label : ℝ) :
    (standardCircle label + direction.val.1 label) * star (standardCircle label + direction.val.1 label) *
      (standardCircleTangent label + direction.val.2.val.1 label) =
    (standardCircleTangent label + direction.val.2.val.1 label) +
      2 * Complex.I * (standardCircle label * ((star (standardCircle label) * direction.val.1 label).re : ℂ)) +
      (direction.val.1 label * star (direction.val.1 label) * standardCircleTangent label +
        (direction.val.1 label * star (standardCircle label) + standardCircle label * star (direction.val.1 label)) *
          direction.val.2.val.1 label +
        direction.val.1 label * star (direction.val.1 label) * direction.val.2.val.1 label) := by
  have unitProduct : standardCircle label * star (standardCircle label) = 1 := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq, standardCircle_norm, one_pow, Complex.ofReal_one,
      mul_comm] using (Complex.normSq_eq_conj_mul_self (z := standardCircle label)).symm
  have realPart : 2 * ((star (standardCircle label) * direction.val.1 label).re : ℂ) =
      star (standardCircle label) * direction.val.1 label + standardCircle label * star (direction.val.1 label) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring
  rw [show 2 * Complex.I * (standardCircle label * ((star (standardCircle label) * direction.val.1 label).re : ℂ)) =
    Complex.I * standardCircle label * (2 * ((star (standardCircle label) * direction.val.1 label).re : ℂ)) by ring,
    realPart]
  simp only [star_add, standardCircleTangent]
  linear_combination (Complex.I * standardCircle label + direction.val.2.val.1 label) * unitProduct

theorem disk_first_moment_quadratic_remainder_bound (direction : PeriodicC1HolderHalf) :
    ‖contourPolynomialMoment 1 (standardCircleBanach + direction) -
      (2 * Real.pi : ℝ) • diskRadialFirstMode direction‖ ≤
        Real.pi * (3 + ‖direction‖) * ‖direction‖ ^ 2 := by
  let linear := fun label : ℝ => standardCircle label *
    ((star (standardCircle label) * direction.val.1 label).re : ℂ)
  let remainder := fun label : ℝ =>
    direction.val.1 label * star (direction.val.1 label) * standardCircleTangent label +
      (direction.val.1 label * star (standardCircle label) + standardCircle label * star (direction.val.1 label)) *
        direction.val.2.val.1 label +
      direction.val.1 label * star (direction.val.1 label) * direction.val.2.val.1 label
  have circleContinuous : Continuous standardCircle :=
    continuous_iff_continuousAt.mpr fun label => (standardCircle_derivative label).continuousAt
  have tangentContinuous : Continuous standardCircleTangent :=
    continuous_iff_continuousAt.mpr fun label => (standardCircleTangent_derivative label).continuousAt
  have linearContinuous : Continuous linear := circleContinuous.mul
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (circleContinuous.star.mul direction.val.1.continuous)))
  have remainderContinuous : Continuous remainder := by dsimp only [remainder]; fun_prop
  have identity : contourPolynomialMoment 1 (standardCircleBanach + direction) -
      (2 * Real.pi : ℝ) • diskRadialFirstMode direction =
        (-Complex.I / 2) * ∫ label in (-Real.pi)..Real.pi, remainder label := by
    rw [contourPolynomialMoment_eq_integral]
    simp only [pow_one]
    change (-Complex.I / 2) * (∫ label in (-Real.pi)..Real.pi,
      (standardCircle label + direction.val.1 label) * star (standardCircle label + direction.val.1 label) *
        (standardCircleTangent label + direction.val.2.val.1 label)) - _ = _
    simp_rw [disk_first_moment_integrand_expansion]
    change (-Complex.I / 2) * (∫ label in (-Real.pi)..Real.pi,
      ((standardCircleTangent label + direction.val.2.val.1 label) + (2 * Complex.I) * linear label) +
        remainder label) - _ = _
    rw [intervalIntegral.integral_add
      ((tangentContinuous.add direction.val.2.val.1.continuous).add
        (continuous_const.mul linearContinuous) |>.intervalIntegrable _ _) (remainderContinuous.intervalIntegrable _ _),
      intervalIntegral.integral_add ((tangentContinuous.add direction.val.2.val.1.continuous).intervalIntegrable _ _)
        ((continuous_const.mul linearContinuous).intervalIntegrable _ _)]
    change (-Complex.I / 2) * (((∫ label in (-Real.pi)..Real.pi,
      (standardCircleBanach + direction).val.2.val.1 label) +
        ∫ label in (-Real.pi)..Real.pi, (2 * Complex.I) * linear label) +
          ∫ label in (-Real.pi)..Real.pi, remainder label) - _ = _
    rw [integral_contourTangent_period_zero, zero_add, intervalIntegral.integral_const_mul]
    unfold diskRadialFirstMode
    rw [smul_smul, mul_one_div_cancel (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul]
    change (-Complex.I / 2) * ((2 * Complex.I) * (∫ label in (-Real.pi)..Real.pi, linear label) +
      ∫ label in (-Real.pi)..Real.pi, remainder label) - (∫ label in (-Real.pi)..Real.pi, linear label) = _
    have square : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination -(∫ label in (-Real.pi)..Real.pi, linear label) * square
  rw [identity, norm_mul]
  have remainderBound (label : ℝ) : ‖remainder label‖ ≤ (3 + ‖direction‖) * ‖direction‖ ^ 2 := by
    have values := PeriodicC1HolderHalf.value_bound direction label
    have speeds := PeriodicC1HolderHalf.speed_bound direction label
    have first : ‖direction.val.1 label * star (direction.val.1 label) * standardCircleTangent label‖ ≤ ‖direction‖ ^ 2 := by
      simp only [norm_mul, norm_star, standardCircleTangent_norm, mul_one]
      nlinarith [sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr values]
    have middle : ‖(direction.val.1 label * star (standardCircle label) + standardCircle label * star (direction.val.1 label)) *
        direction.val.2.val.1 label‖ ≤ 2 * ‖direction‖ ^ 2 := by
      rw [norm_mul]
      have pair := norm_add_le (direction.val.1 label * star (standardCircle label))
        (standardCircle label * star (direction.val.1 label))
      simp only [norm_mul, norm_star, standardCircle_norm, mul_one, one_mul] at pair
      calc
        _ ≤ (‖direction.val.1 label‖ + ‖direction.val.1 label‖) * ‖direction.val.2.val.1 label‖ :=
          mul_le_mul_of_nonneg_right pair (norm_nonneg _)
        _ ≤ (‖direction‖ + ‖direction‖) * ‖direction‖ := by gcongr
        _ = _ := by ring
    have last : ‖direction.val.1 label * star (direction.val.1 label) * direction.val.2.val.1 label‖ ≤ ‖direction‖ ^ 3 := by
      simp only [norm_mul, norm_star]
      calc
        _ ≤ ‖direction‖ * ‖direction‖ * ‖direction‖ := by gcongr
        _ = _ := by ring
    exact (norm_add_le _ _).trans (by
      have combined := norm_add_le
        (direction.val.1 label * star (direction.val.1 label) * standardCircleTangent label)
        ((direction.val.1 label * star (standardCircle label) + standardCircle label * star (direction.val.1 label)) *
          direction.val.2.val.1 label)
      nlinarith)
  have integralBound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -Real.pi) (b := Real.pi) (f := remainder) (C := (3 + ‖direction‖) * ‖direction‖ ^ 2)
    (fun label _ => remainderBound label)
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at integralBound
  have coefficient : ‖-Complex.I / 2‖ = (1 / 2 : ℝ) := by simp
  rw [coefficient]
  nlinarith

theorem diskRadialFirstMode_norm_le_of_first_moment_zero (direction : PeriodicC1HolderHalf)
    (centered : contourPolynomialMoment 1 (standardCircleBanach + direction) = 0) :
    ‖diskRadialFirstMode direction‖ ≤ ((3 + ‖direction‖) / 2) * ‖direction‖ ^ 2 := by
  have estimate := disk_first_moment_quadratic_remainder_bound direction
  rw [centered, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)] at estimate
  apply (mul_le_mul_left (by positivity : 0 < 2 * Real.pi)).mp
  convert estimate using 1 <;> ring

theorem diskRadialFirstMode_norm_le_of_domain_centered
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (centered : (∫ position in nearCircleInterior data small, position) = 0) :
    ‖diskRadialFirstMode (data - standardCircleBanach)‖ ≤
      ((3 + ‖data - standardCircleBanach‖) / 2) * ‖data - standardCircleBanach‖ ^ 2 := by
  apply diskRadialFirstMode_norm_le_of_first_moment_zero
  have reconstruction : standardCircleBanach + (data - standardCircleBanach) = data := by abel
  rw [reconstruction, contourPolynomialMoment_one_eq_domain_integral data small, centered]

theorem diskRadialFirstMode_norm_le_of_true_centroid_zero
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (centered : contourCentroidFunctional data = 0) :
    ‖diskRadialFirstMode (data - standardCircleBanach)‖ ≤
      ((3 + ‖data - standardCircleBanach‖) / 2) * ‖data - standardCircleBanach‖ ^ 2 := by
  apply diskRadialFirstMode_norm_le_of_first_moment_zero
  have reconstruction : standardCircleBanach + (data - standardCircleBanach) = data := by abel
  rw [reconstruction]
  have nonzero : (contourAreaFunctional data : ℂ) ≠ 0 := by
    exact_mod_cast (contourAreaFunctional_pos data small).ne'
  have identity := congrArg (fun value : ℂ => value * (contourAreaFunctional data : ℂ)) centered
  simpa only [contourCentroidFunctional, div_mul_cancel₀ _ nonzero, zero_mul] using identity

end

end EulerNonuniqueness.Paper
