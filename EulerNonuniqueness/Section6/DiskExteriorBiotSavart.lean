import EulerNonuniqueness.Section6.DiskPolarIntegration
import EulerNonuniqueness.Section8.BiotSavart
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals

noncomputable section

open Set MeasureTheory
open scoped ComplexConjugate

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

theorem integral_circle_inverse_source (position : ℂ) {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius) (outside : radius < ‖position‖) :
    (∫ angle in (0 : ℝ)..2 * Real.pi, (position - circleMap 0 radius angle)⁻¹) =
      ((2 * Real.pi : ℝ) : ℂ) * position⁻¹ := by
  rcases radiusNonnegative.eq_or_lt with zero | positive
  · subst radius
    simp [circleMap, intervalIntegral.integral_const, Complex.real_smul]
  have nonzero (source : ℂ) (inside : source ∈ Metric.closedBall 0 radius) : position - source ≠ 0 := by
    intro equality
    have bound : ‖source‖ ≤ radius := by simpa using inside
    rw [← sub_eq_zero.mp equality] at bound
    linarith
  have functionContinuous : ContinuousOn (fun source : ℂ => (position - source)⁻¹)
      (Metric.closedBall 0 radius) :=
    (continuous_const.sub continuous_id).continuousOn.inv₀ nonzero
  have functionDifferentiable : ∀ source ∈ Metric.ball (0 : ℂ) radius \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun current => (position - current)⁻¹) source := by
    intro source inside
    exact (differentiableAt_const position |>.sub differentiableAt_id).inv
      (nonzero source (Metric.ball_subset_closedBall inside.1))
  have formula := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (c := 0) (w := 0) (R := radius) (f := fun source : ℂ => (position - source)⁻¹)
    (s := ∅) Set.countable_empty (by simpa using positive) functionContinuous functionDifferentiable
  have integrand (angle : ℝ) :
      deriv (circleMap 0 radius) angle •
        ((circleMap 0 radius angle - 0)⁻¹ •
          (position - circleMap 0 radius angle)⁻¹) =
      Complex.I * (position - circleMap 0 radius angle)⁻¹ := by
    have circleNonzero : circleMap 0 radius angle ≠ 0 := by simp [positive.ne']
    rw [deriv_circleMap]
    simp only [sub_zero, smul_eq_mul]
    calc
      _ = (circleMap 0 radius angle * (circleMap 0 radius angle)⁻¹) *
        (Complex.I * (position - circleMap 0 radius angle)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ circleNonzero, one_mul]
  change (∫ angle in (0 : ℝ)..2 * Real.pi,
    deriv (circleMap 0 radius) angle •
      ((circleMap 0 radius angle - 0)⁻¹ •
        (position - circleMap 0 radius angle)⁻¹)) = _ at formula
  simp_rw [integrand] at formula
  rw [intervalIntegral.integral_const_mul] at formula
  have identity : Complex.I * (∫ angle in (0 : ℝ)..2 * Real.pi,
      (position - circleMap 0 radius angle)⁻¹) =
      Complex.I * (((2 * Real.pi : ℝ) : ℂ) * position⁻¹) := by
    convert formula using 1
    simp only [sub_zero, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  exact mul_left_cancel₀ Complex.I_ne_zero identity

theorem integral_circle_inverse_source_symmetric (position : ℂ) {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius) (outside : radius < ‖position‖) :
    (∫ angle in Ioo (-Real.pi) Real.pi, (position - (radius : ℂ) * standardCircle angle)⁻¹) =
      ((2 * Real.pi : ℝ) : ℂ) * position⁻¹ := by
  have periodic : Function.Periodic (fun angle => (position - circleMap 0 radius angle)⁻¹) (2 * Real.pi) :=
    (periodic_circleMap 0 radius).comp (fun source => (position - source)⁻¹)
  have transfer := periodic.intervalIntegral_add_eq (-Real.pi) 0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add,
    integral_circle_inverse_source position radiusNonnegative outside] at transfer
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo] at transfer
  simpa only [circleMap, zero_add, standardCircle, mul_comm] using transfer

theorem integral_ball_inverse_source (position : ℂ) {radius : ℝ}
    (radiusPositive : 0 < radius) (outside : radius < ‖position‖) :
    (∫ source in Metric.ball (0 : ℂ) radius, (position - source)⁻¹) =
      ((Real.pi * radius ^ 2 : ℝ) : ℂ) * position⁻¹ := by
  have nonzero (source : ℂ) (inside : source ∈ Metric.closedBall 0 radius) : position - source ≠ 0 := by
    intro equality
    have bound : ‖source‖ ≤ radius := by simpa using inside
    rw [← sub_eq_zero.mp equality] at bound
    linarith
  have functionContinuous : ContinuousOn (fun source : ℂ => (position - source)⁻¹)
      (Metric.closedBall 0 radius) :=
    (continuous_const.sub continuous_id).continuousOn.inv₀ nonzero
  rw [integral_ball_polar radiusPositive _ functionContinuous]
  have angular :
      (∫ radial in Ioo (0 : ℝ) radius, ∫ angle in Ioo (-Real.pi) Real.pi,
        radial • (position - (radial : ℂ) * standardCircle angle)⁻¹) =
      ∫ radial in Ioo (0 : ℝ) radius, radial • (((2 * Real.pi : ℝ) : ℂ) * position⁻¹) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with radial member
    rw [integral_smul, integral_circle_inverse_source_symmetric position member.1.le
      (member.2.trans outside)]
  rw [angular, integral_smul_const]
  have radialIntegral : (∫ radial in Ioo (0 : ℝ) radius, radial) = radius ^ 2 / 2 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le radiusPositive.le]
    simp [integral_id]
  rw [radialIntegral, Complex.real_smul]
  push_cast
  ring

theorem integral_centeredBall_biotSavartKernel_exterior (position : ℂ) {radius : ℝ}
    (radiusPositive : 0 < radius) (outside : radius < ‖position‖) :
    (∫ source in Metric.ball (0 : ℂ) radius, biotSavartKernel (position - source)) =
      (Real.pi * radius ^ 2) • biotSavartKernel position := by
  have integrand : (fun source : ℂ => biotSavartKernel (position - source)) =
      fun source => (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * conj ((position - source)⁻¹) := by
    funext source
    rw [biotSavartKernel_eq_conj_inv]
    simp only [map_inv₀]
  rw [integrand, integral_const_mul, integral_conj,
    integral_ball_inverse_source position radiusPositive outside, biotSavartKernel_eq_conj_inv,
    Complex.real_smul]
  simp only [map_mul, map_inv₀, Complex.conj_ofReal]
  ring

theorem integral_ball_biotSavartKernel_exterior (center position : ℂ) {radius : ℝ}
    (radiusPositive : 0 < radius) (outside : radius < ‖position - center‖) :
    (∫ source in Metric.ball center radius, biotSavartKernel (position - source)) =
      (Real.pi * radius ^ 2) • biotSavartKernel (position - center) := by
  have imageBall : (fun source : ℂ => center + source) '' Metric.ball (0 : ℂ) radius =
      Metric.ball center radius := by
    ext source
    constructor
    · rintro ⟨normalized, member, rfl⟩
      simpa [Metric.mem_ball, dist_eq_norm] using member
    · intro member
      refine ⟨source - center, ?_, add_sub_cancel _ _⟩
      simpa [Metric.mem_ball, dist_eq_norm] using member
  have translation := (measurePreserving_add_left (volume : Measure ℂ) center).setIntegral_image_emb
    (Homeomorph.addLeft center).toMeasurableEquiv.measurableEmbedding
    (fun source => biotSavartKernel (position - source)) (Metric.ball (0 : ℂ) radius)
  rw [imageBall] at translation
  have difference (source : ℂ) : position - (center + source) = (position - center) - source := by abel
  simp_rw [difference] at translation
  rw [translation, integral_centeredBall_biotSavartKernel_exterior (position - center) radiusPositive outside]

theorem biotSavart_disk_exterior (center position : ℂ) {radius : ℝ}
    (radiusPositive : 0 < radius) (outside : radius < ‖position - center‖) (density : ℝ) :
    biotSavart ((Metric.ball center radius).indicator (fun _ => density)) position =
      (density * (Real.pi * radius ^ 2)) • biotSavartKernel (position - center) := by
  have velocity : biotSavart ((Metric.ball center radius).indicator (fun _ => density)) position =
      density • (∫ source in Metric.ball center radius, biotSavartKernel (position - source)) := by
    rw [← integral_smul, ← integral_indicator measurableSet_ball]
    unfold biotSavart
    apply integral_congr_ae
    filter_upwards [] with source
    by_cases member : source ∈ Metric.ball center radius <;> simp [member]
  rw [velocity, integral_ball_biotSavartKernel_exterior center position radiusPositive outside, smul_smul]

end EulerNonuniqueness.Section6
