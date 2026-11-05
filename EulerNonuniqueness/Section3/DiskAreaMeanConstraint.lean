import EulerNonuniqueness.Section3.ContourAnalyticArea
import EulerNonuniqueness.Section3.ContourBiotSavartAdvection
import EulerNonuniqueness.Section3.CircleBanach
import Mathlib.Analysis.Complex.RealDeriv

namespace EulerNonuniqueness.Paper

open MeasureTheory

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance areaMeanHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance areaMeanC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

def diskRadialMean (direction : PeriodicC1HolderHalf) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ label in (-Real.pi)..Real.pi,
    (star (standardCircle label) * direction.val.1 label).re

theorem diskArea_cross_integral (direction : PeriodicC1HolderHalf) :
    (∫ label in (-Real.pi)..Real.pi,
      contourAreaPair (standardCircle label) (direction.val.2.val.1 label)) =
    ∫ label in (-Real.pi)..Real.pi, (star (standardCircle label) * direction.val.1 label).re := by
  have circleContinuous : Continuous standardCircle :=
    continuous_iff_continuousAt.mpr fun label => (standardCircle_derivative label).continuousAt
  let radial := fun label : ℝ => (star (standardCircle label) * direction.val.1 label).re
  let mixed := fun label : ℝ => contourAreaPair (standardCircle label) (direction.val.2.val.1 label)
  have radialContinuous : Continuous radial := Complex.continuous_re.comp (circleContinuous.star.mul direction.val.1.continuous)
  have mixedContinuous : Continuous mixed :=
    continuous_contourAreaPair.comp (circleContinuous.prodMk direction.val.2.val.1.continuous)
  have actual (label : ℝ) : HasDerivAt
      (fun current => contourAreaPair (standardCircle current) (direction.val.1 current))
      (-radial label + mixed label) label := by
    have product := (standardCircle_derivative label).star.mul (PeriodicC1HolderHalf.hasDerivAt direction label)
    have result := Complex.imCLM.hasFDerivAt.comp_hasDerivAt label product
    apply result.congr_deriv
    change (star (standardCircleTangent label) * direction.val.1 label +
      star (standardCircle label) * direction.val.2.val.1 label).im = _
    simp only [radial, mixed, contourAreaPair, standardCircleTangent, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.I_re, Complex.I_im]
    ring
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun label _ => actual label)
    ((radialContinuous.neg.add mixedContinuous).intervalIntegrable (-Real.pi) Real.pi)
  have directionEndpoint : direction.val.1 Real.pi = direction.val.1 (-Real.pi) := by
    have periodic := PeriodicC1HolderHalf.periodic direction (-Real.pi)
    simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using periodic
  have circleEndpoint : standardCircle Real.pi = standardCircle (-Real.pi) := by
    have periodic := standardCircle_periodic (-Real.pi)
    simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using periodic
  rw [directionEndpoint, circleEndpoint, sub_self,
    intervalIntegral.integral_add ((radialContinuous.neg).intervalIntegrable _ _) (mixedContinuous.intervalIntegrable _ _),
    intervalIntegral.integral_neg] at integral
  change (∫ label in (-Real.pi)..Real.pi, mixed label) = ∫ label in (-Real.pi)..Real.pi, radial label
  linarith

theorem contourAreaFunctional_circle_add (direction : PeriodicC1HolderHalf) :
    contourAreaFunctional (standardCircleBanach + direction) =
      Real.pi + (2 * Real.pi) * diskRadialMean direction + contourAreaFunctional direction := by
  let radial := fun label : ℝ => (star (standardCircle label) * direction.val.1 label).re
  let mixed := fun label : ℝ => contourAreaPair (standardCircle label) (direction.val.2.val.1 label)
  let quadratic := fun label : ℝ => contourAreaPair (direction.val.1 label) (direction.val.2.val.1 label)
  have circleContinuous : Continuous standardCircle :=
    continuous_iff_continuousAt.mpr fun label => (standardCircle_derivative label).continuousAt
  have radialContinuous : Continuous radial := Complex.continuous_re.comp (circleContinuous.star.mul direction.val.1.continuous)
  have mixedContinuous : Continuous mixed :=
    continuous_contourAreaPair.comp (circleContinuous.prodMk direction.val.2.val.1.continuous)
  have quadraticContinuous : Continuous quadratic :=
    continuous_contourAreaPair.comp (direction.val.1.continuous.prodMk direction.val.2.val.1.continuous)
  have circlePair (label : ℝ) : contourAreaPair (standardCircle label) (standardCircleTangent label) = 1 := by
    have unitProduct : star (standardCircle label) * standardCircle label = 1 := by
      simpa only [Complex.star_def, Complex.normSq_eq_norm_sq, standardCircle_norm, one_pow, Complex.ofReal_one] using
        (Complex.normSq_eq_conj_mul_self (z := standardCircle label)).symm
    unfold contourAreaPair standardCircleTangent
    rw [show star (standardCircle label) * (Complex.I * standardCircle label) =
      Complex.I * (star (standardCircle label) * standardCircle label) by ring, unitProduct]
    simp
  have expansion (label : ℝ) :
      contourAreaPair ((standardCircleBanach + direction).val.1 label)
        ((standardCircleBanach + direction).val.2.val.1 label) =
      ((1 + mixed label) + radial label) + quadratic label := by
    change contourAreaPair (standardCircle label + direction.val.1 label)
      (standardCircleTangent label + direction.val.2.val.1 label) = _
    have otherCross : contourAreaPair (direction.val.1 label) (standardCircleTangent label) = radial label := by
      simp only [contourAreaPair, standardCircleTangent, radial, Complex.mul_re, Complex.mul_im,
        Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im]
      ring
    have additive : contourAreaPair (standardCircle label + direction.val.1 label)
        (standardCircleTangent label + direction.val.2.val.1 label) =
      ((contourAreaPair (standardCircle label) (standardCircleTangent label) + mixed label) +
        contourAreaPair (direction.val.1 label) (standardCircleTangent label)) + quadratic label := by
      simp only [contourAreaPair, mixed, quadratic, Complex.star_def, map_add, add_mul, mul_add, Complex.add_im]
      ring
    rw [additive, circlePair, otherCross]
  rw [contourAreaFunctional_eq_boundary, contourAreaFunctional_eq_boundary]
  simp_rw [expansion]
  rw [intervalIntegral.integral_add ((continuous_const.add mixedContinuous).add radialContinuous |>.intervalIntegrable _ _)
      (quadraticContinuous.intervalIntegrable _ _),
    intervalIntegral.integral_add ((continuous_const.add mixedContinuous).intervalIntegrable _ _)
      (radialContinuous.intervalIntegrable _ _),
    intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _) (mixedContinuous.intervalIntegrable _ _)]
  have cross := diskArea_cross_integral direction
  change (∫ label in (-Real.pi)..Real.pi, mixed label) = ∫ label in (-Real.pi)..Real.pi, radial label at cross
  rw [cross, intervalIntegral.integral_const]
  unfold diskRadialMean
  dsimp only [radial, quadratic]
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero]
  ring

theorem contourAreaFunctional_abs_le (direction : PeriodicC1HolderHalf) :
    |contourAreaFunctional direction| ≤ Real.pi * ‖direction‖ ^ 2 := by
  have bound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -Real.pi) (b := Real.pi)
    (f := fun label => contourAreaPair (direction.val.1 label) (direction.val.2.val.1 label))
    (C := ‖direction‖ ^ 2) (fun label _ => by
      apply (norm_contourAreaPair_le _ _).trans
      have values := PeriodicC1HolderHalf.value_bound direction label
      have speeds := PeriodicC1HolderHalf.speed_bound direction label
      nlinarith [mul_le_mul values speeds (norm_nonneg _) (norm_nonneg direction)])
  rw [Real.norm_eq_abs, show Real.pi - -Real.pi = 2 * Real.pi by ring,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)] at bound
  rw [contourAreaFunctional_eq_boundary, abs_mul, abs_of_pos (by norm_num : 0 < (1 / 2 : ℝ))]
  nlinarith

theorem diskRadialMean_eq_of_area (direction : PeriodicC1HolderHalf)
    (area : contourAreaFunctional (standardCircleBanach + direction) = Real.pi) :
    diskRadialMean direction = -(1 / (2 * Real.pi)) * contourAreaFunctional direction := by
  have expansion := contourAreaFunctional_circle_add direction
  rw [area] at expansion
  field_simp [Real.pi_ne_zero]
  nlinarith

theorem diskRadialMean_abs_le_of_area (direction : PeriodicC1HolderHalf)
    (area : contourAreaFunctional (standardCircleBanach + direction) = Real.pi) :
    |diskRadialMean direction| ≤ (1 / 2 : ℝ) * ‖direction‖ ^ 2 := by
  rw [diskRadialMean_eq_of_area direction area, abs_mul, abs_neg,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  have bound := contourAreaFunctional_abs_le direction
  have scaled := mul_le_mul_of_nonneg_left bound (show 0 ≤ 1 / (2 * Real.pi) by positivity)
  convert scaled using 1 <;> field_simp <;> ring

theorem diskRadialMean_abs_le_of_domain_area (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (area : (volume (nearCircleInterior data small)).toReal = Real.pi) :
    |diskRadialMean (data - standardCircleBanach)| ≤ (1 / 2 : ℝ) * ‖data - standardCircleBanach‖ ^ 2 := by
  apply diskRadialMean_abs_le_of_area
  have reconstruction : standardCircleBanach + (data - standardCircleBanach) = data := by abel
  rw [reconstruction, contourAreaFunctional_eq_domain_area data small, area]

end

end EulerNonuniqueness.Paper
