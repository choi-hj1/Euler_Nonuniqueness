import EulerNonuniqueness.Section6.PaperQuadrupoleStrainDerivative
import EulerNonuniqueness.Section6.DiskExteriorBiotSavart

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem biotSavartKernel_hasFDerivAt {position center : ℂ} (nonzero : position - center ≠ 0) :
    HasFDerivAt (fun current => biotSavartKernel (current - center))
      (biotSavartKernelStrain position center • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) position := by
  have conjugate : HasFDerivAt (fun current : ℂ => star (current - center))
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) position := by
    simpa only [ContinuousLinearMap.comp_id] using
      Complex.conjCLE.hasFDerivAt.comp position ((hasFDerivAt_id position).sub_const center)
  have inverse := ((hasDerivAt_id (star (position - center))).inv (star_ne_zero.mpr nonzero)).const_mul
    (Complex.I / ((2 * Real.pi : ℝ) : ℂ))
  have derivative := inverse.comp_hasFDerivAt position conjugate
  convert derivative using 1
  · funext current
    simp only [Function.comp_apply, biotSavartKernel_eq_conj_inv, map_inv₀, starRingEnd_apply, id_eq]
  · ext increment
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, biotSavartKernelStrain, id_eq]
    ring

theorem integral_ball_biotSavartKernelStrain_exterior (center position : ℂ) {radius : ℝ}
    (radiusPositive : 0 < radius) (outside : radius < ‖position - center‖) :
    (∫ source in Metric.ball center radius, biotSavartKernelStrain position source) =
      (Real.pi * radius ^ 2) • biotSavartKernelStrain position center := by
  have positionPositive : 0 < ‖position - center‖ := radiusPositive.trans outside
  have separation (source : ℂ) (member : source ∈ Metric.ball center radius) :
      ‖position - center‖ - radius ≤ ‖position - source‖ := by
    have sourceBound : ‖source - center‖ < radius := by simpa only [Metric.mem_ball, dist_eq_norm] using member
    have triangle := norm_add_le (position - source) (source - center)
    rw [sub_add_sub_cancel] at triangle
    linarith
  have diskDerivative := indicator_biotSavart_hasFDerivAt_of_separation measurableSet_ball measure_ball_lt_top 1
    (by linarith : 0 < ‖position - center‖ - radius) separation
  have pointDerivative := (biotSavartKernel_hasFDerivAt (norm_pos_iff.mp positionPositive)).const_smul
    (Real.pi * radius ^ 2)
  have eventuallyOutside : ∀ᶠ current : ℂ in 𝓝 position, radius < ‖current - center‖ :=
    ((continuous_id.sub continuous_const).norm.continuousAt.tendsto).eventually (eventually_gt_nhds outside)
  have eventuallyEqual : biotSavart ((Metric.ball center radius).indicator (fun _ => (1 : ℝ))) =ᶠ[𝓝 position]
      (fun current => (Real.pi * radius ^ 2) • biotSavartKernel (current - center)) := by
    filter_upwards [eventuallyOutside] with current member
    simpa only [one_mul] using biotSavart_disk_exterior center current radiusPositive member 1
  have diskPointDerivative := pointDerivative.congr_of_eventuallyEq eventuallyEqual
  have identity := congrArg (fun operator : ℂ →L[ℝ] ℂ => operator 1) (diskDerivative.unique diskPointDerivative)
  have conjugateOne : (Complex.conjCLE : ℂ →L[ℝ] ℂ) 1 = 1 := by
    change star (1 : ℂ) = 1
    exact star_one ℂ
  simpa only [ContinuousLinearMap.smul_apply, one_smul, Complex.real_smul, Complex.conjCLE_apply,
    conjugateOne, smul_eq_mul, mul_one] using identity

end EulerNonuniqueness.Section6
