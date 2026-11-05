import EulerNonuniqueness.Section3.DiskAreaDerivative
import EulerNonuniqueness.Section3.MovingCentroidGaugeConservation

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance centroidCircleHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance centroidCircleC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

private theorem affine_line_derivative {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (base direction : Space) : HasDerivAt (fun scalar : ℝ => base + scalar • direction) direction 0 := by
  simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const direction).const_add base

private theorem linear_affine_line_derivative {Space Target : Type*}
    [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (operator : Space →L[ℝ] Target) (base direction : Space) :
    HasDerivAt (fun scalar : ℝ => operator (base + scalar • direction)) (operator direction) 0 := by
  exact HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := Space) (E := Target) 0
    operator.hasFDerivAt (affine_line_derivative base direction)

private theorem differentiable_affine_line_derivative {Space Target : Type*}
    [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (function : Space → Target) (base direction : Space)
    (differentiable : DifferentiableAt ℝ function base) :
    HasDerivAt (fun scalar : ℝ => function (base + scalar • direction))
      ((fderiv ℝ function base) direction) 0 := by
  have outer : HasFDerivAt function (fderiv ℝ function base) (base + (0 : ℝ) • direction) := by
    simpa only [zero_smul, add_zero] using differentiable.hasFDerivAt
  exact HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := Space) (E := Target) 0
    outer (affine_line_derivative base direction)

theorem contourPolynomialMoment_one_circle_line_hasDerivAt (direction : PeriodicC1HolderHalf) :
    HasDerivAt (fun scalar : ℝ => contourPolynomialMoment 1 (standardCircleBanach + scalar • direction))
      ((-Complex.I / 2) * ∫ label in (-Real.pi)..Real.pi,
        direction.val.1 label * star (standardCircleBanach.val.1 label) * standardCircleBanach.val.2.val.1 label +
        standardCircleBanach.val.1 label * star (direction.val.1 label) * standardCircleBanach.val.2.val.1 label +
        standardCircleBanach.val.1 label * star (standardCircleBanach.val.1 label) * direction.val.2.val.1 label) 0 := by
  have valueJet := linear_affine_line_derivative contourValueFunctionCLM standardCircleBanach direction
  have conjugateJet := linear_affine_line_derivative (contourValueFunctionCLM.comp c1ConjugateCLM) standardCircleBanach direction
  have tangentJet := linear_affine_line_derivative contourTangentFunctionCLM standardCircleBanach direction
  have productJet := (valueJet.mul conjugateJet).mul tangentJet
  have integralJet := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := ℝ →ᵇ ℂ) (E := ℂ) 0
    (boundedIntervalIntegral (-Real.pi) Real.pi).hasFDerivAt productJet
  have actual := integralJet.const_mul (-Complex.I / 2)
  convert actual using 1
  · funext scalar
    simp only [contourPolynomialMoment, pow_one, Function.comp_apply,
      ContinuousLinearMap.comp_apply]
  · congr 1
    apply intervalIntegral.integral_congr
    intro label _inside
    change _ = ((direction.val.1 label * star ((standardCircleBanach + (0 : ℝ) • direction).val.1 label) +
      (standardCircleBanach + (0 : ℝ) • direction).val.1 label * star (direction.val.1 label)) *
      (standardCircleBanach + (0 : ℝ) • direction).val.2.val.1 label +
      ((standardCircleBanach + (0 : ℝ) • direction).val.1 label *
        star ((standardCircleBanach + (0 : ℝ) • direction).val.1 label)) * direction.val.2.val.1 label)
    simp only [zero_smul, add_zero]
    ring

theorem contourPolynomialMoment_one_circle_derivative (direction : PeriodicC1HolderHalf) :
    (fderiv ℝ (contourPolynomialMoment 1) standardCircleBanach) direction =
      (1 / 2 : ℂ) * ∫ label in (-Real.pi)..Real.pi,
        direction.val.1 label + standardCircleBanach.val.1 label ^ 2 * star (direction.val.1 label) := by
  have derivative := contourPolynomialMoment_one_circle_line_hasDerivAt direction
  have integrandIdentity :
      (fun label => direction.val.1 label * star (standardCircleBanach.val.1 label) * standardCircleBanach.val.2.val.1 label +
        standardCircleBanach.val.1 label * star (direction.val.1 label) * standardCircleBanach.val.2.val.1 label +
        standardCircleBanach.val.1 label * star (standardCircleBanach.val.1 label) * direction.val.2.val.1 label) =
      fun label => Complex.I * (direction.val.1 label +
        standardCircleBanach.val.1 label ^ 2 * star (direction.val.1 label)) + direction.val.2.val.1 label := by
    funext label
    have unit : standardCircleBanach.val.1 label * star (standardCircleBanach.val.1 label) = (1 : ℂ) := by
      change standardCircle label * star (standardCircle label) = 1
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, standardCircle_norm]
      norm_num
    change direction.val.1 label * star (standardCircle label) * (Complex.I * standardCircle label) +
      standardCircle label * star (direction.val.1 label) * (Complex.I * standardCircle label) +
      standardCircle label * star (standardCircle label) * direction.val.2.val.1 label = _
    change standardCircle label * star (standardCircle label) = 1 at unit
    calc
      _ = Complex.I * direction.val.1 label * (standardCircle label * star (standardCircle label)) +
          Complex.I * standardCircle label ^ 2 * star (direction.val.1 label) +
          (standardCircle label * star (standardCircle label)) * direction.val.2.val.1 label := by ring
      _ = _ := by
        change _ = Complex.I * (direction.val.1 label +
          standardCircle label ^ 2 * star (direction.val.1 label)) + direction.val.2.val.1 label
        rw [unit]
        ring
  rw [integrandIdentity, intervalIntegral.integral_add
    ((continuous_const.mul (direction.val.1.continuous.add
      ((standardCircleBanach.val.1.continuous.pow 2).mul direction.val.1.continuous.star))).intervalIntegrable _ _)
    (direction.val.2.val.1.continuous.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    contour_tangent_integral_zero, add_zero] at derivative
  have outer : HasFDerivAt (contourPolynomialMoment 1)
      (fderiv ℝ (contourPolynomialMoment 1) standardCircleBanach)
      (standardCircleBanach + (0 : ℝ) • direction) := by
    simpa only [zero_smul, add_zero] using
      (analyticAt_contourPolynomialMoment 1 standardCircleBanach).differentiableAt.hasFDerivAt
  have actual := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf) (E := ℂ) 0
    outer
    (affine_line_derivative standardCircleBanach direction)
  have identity := actual.unique derivative
  simp only [zero_smul, add_zero] at identity
  rw [identity]
  have imaginary : (-Complex.I / 2) * Complex.I = (1 / 2 : ℂ) := by
    calc
      _ = -(Complex.I ^ 2) / 2 := by ring
      _ = _ := by rw [Complex.I_sq]; norm_num
  rw [← mul_assoc, imaginary]

theorem contourCentroidFunctional_circle_derivative (direction : PeriodicC1HolderHalf) :
    (fderiv ℝ contourCentroidFunctional standardCircleBanach) direction =
      (1 / (2 * (Real.pi : ℂ))) * ∫ label in (-Real.pi)..Real.pi,
        direction.val.1 label + standardCircleBanach.val.1 label ^ 2 * star (direction.val.1 label) := by
  have piNonzero : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have momentZero : contourPolynomialMoment 1 standardCircleBanach = 0 := by
    have identity := contourCentroidFunctional_standardCircle_zero
    rw [contourCentroidFunctional, contourAreaFunctional_standardCircle] at identity
    exact (div_eq_zero_iff.mp identity).resolve_right piNonzero
  have momentJet := differentiable_affine_line_derivative (contourPolynomialMoment 1)
    standardCircleBanach direction
    (analyticAt_contourPolynomialMoment 1 standardCircleBanach).differentiableAt
  have areaJet := differentiable_affine_line_derivative contourAreaFunctional
    standardCircleBanach direction (analyticAt_contourAreaFunctional standardCircleBanach).differentiableAt
  have denominatorJet := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := ℝ) (E := ℂ) 0
    Complex.ofRealCLM.hasFDerivAt areaJet
  have denominatorNonzero : (contourAreaFunctional (standardCircleBanach + (0 : ℝ) • direction) : ℂ) ≠ 0 := by
    simpa only [zero_smul, add_zero, contourAreaFunctional_standardCircle] using piNonzero
  have quotientJet := momentJet.div denominatorJet denominatorNonzero
  have small : ‖standardCircleBanach - standardCircleBanach‖ < (1 / 3 : ℝ) := by
    change ‖standardCircleBanach.val - standardCircleBanach.val‖ < (1 / 3 : ℝ)
    rw [sub_self, norm_zero]
    norm_num
  have actual := differentiable_affine_line_derivative contourCentroidFunctional
    standardCircleBanach direction (analyticAt_contourCentroidFunctional standardCircleBanach small).differentiableAt
  have quotientIdentity : (fun scalar : ℝ => contourCentroidFunctional (standardCircleBanach + scalar • direction)) =
      fun scalar => contourPolynomialMoment 1 (standardCircleBanach + scalar • direction) /
        (contourAreaFunctional (standardCircleBanach + scalar • direction) : ℂ) := rfl
  rw [quotientIdentity] at actual
  have identity := actual.unique quotientJet
  rw [identity]
  simp only [Function.comp_apply, zero_smul, add_zero, momentZero, zero_mul, sub_zero,
    contourAreaFunctional_standardCircle, contourPolynomialMoment_one_circle_derivative]
  field_simp
  <;> ring

end EulerNonuniqueness.Paper
