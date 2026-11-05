import EulerNonuniqueness.Section3.ContourCauchyHolomorphic
import Mathlib.Analysis.Calculus.FDeriv.Analytic

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

def contourCauchyDirectionalDerivative (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) : PeriodicHolderHalf :=
  deriv (fun parameter : ℂ => extendedContourCauchy (data + parameter • direction) density) 0

theorem contourCauchyDirectionalDerivative_hasDerivAt (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    HasDerivAt (fun parameter : ℂ => extendedContourCauchy (data + parameter • direction) density)
      (contourCauchyDirectionalDerivative data direction density) 0 :=
  (analyticAt_extendedContourCauchy_complex_line data direction density small).differentiableAt.hasDerivAt

theorem contourCauchyDirectionalDerivative_value (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    (contourCauchyDirectionalDerivative data direction density).val.1 target =
      ∫ source in (target - Real.pi)..(target + Real.pi),
        (density.val.1 source - density.val.1 target) * contourCauchyKernelVariation data direction target source := by
  obtain ⟨radius, near, smaller⟩ := exists_between (small.trans_le (min_le_right _ _))
  have scalar := contourCauchyTransform_hasDerivAt_complex_parameter data direction density near smaller target
  have vector := (complexHolderEvaluation target).hasFDerivAt.comp_hasDerivAt (0 : ℂ)
    (contourCauchyDirectionalDerivative_hasDerivAt data direction density small)
  have path : LipschitzWith ⟨‖direction‖, norm_nonneg direction⟩
      (fun current : ℂ => data + current • direction - standardCircleBanach) := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    rw [dist_eq_norm (data + first • direction - standardCircleBanach)
      (data + second • direction - standardCircleBanach), dist_eq_norm first second]
    have identity : data + first • direction - standardCircleBanach -
        (data + second • direction - standardCircleBanach) = (first - second) • direction := by
      rw [sub_smul first second direction]
      abel
    rw [identity, norm_smul (first - second) direction]
    exact le_of_eq (mul_comm _ _)
  have nearby : ∀ᶠ current : ℂ in 𝓝 0,
      ‖data + current • direction - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    have continuity : Continuous (fun current : ℂ => ‖data + current • direction - standardCircleBanach‖) :=
      path.continuous.norm
    have initial_small : ‖data + (0 : ℂ) • direction - standardCircleBanach‖ <
        min 1 (2 / (3 * Real.pi)) := by simpa only [zero_smul, add_zero] using small
    exact (continuity.continuousAt (x := (0 : ℂ))).eventually (gt_mem_nhds initial_small)
  have scalar_extended : HasDerivAt
      (fun current : ℂ => (extendedContourCauchy (data + current • direction) density).val.1 target)
      (∫ source in (target - Real.pi)..(target + Real.pi),
        (density.val.1 source - density.val.1 target) * contourCauchyKernelVariation data direction target source) 0 :=
    scalar.congr_of_eventuallyEq (by
    filter_upwards [nearby] with current current_small
    rw [extendedContourCauchy_eq _ _ current_small]
    rfl)
  exact vector.unique scalar_extended

theorem contourCauchyKernelVariation_density_integrable (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) (small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (target : ℝ) :
    IntervalIntegrable (fun source => (density.val.1 source - density.val.1 target) *
      contourCauchyKernelVariation data direction target source) volume (target - Real.pi) (target + Real.pi) := by
  have first := contourCauchyVariationIntegral_integrable data direction density small target
  have second := (contourCauchyKernelVariation_intervalIntegrable data direction small target).const_mul
    (density.val.1 target)
  convert first.sub second using 1
  ext source
  ring

theorem contourCauchyDirectionalDerivative_add (data first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourCauchyDirectionalDerivative data (first + second) density =
      contourCauchyDirectionalDerivative data first density + contourCauchyDirectionalDerivative data second density := by
  apply PeriodicHolderHalf.ext_value
  intro target
  change (contourCauchyDirectionalDerivative data (first + second) density).val.1 target =
    (contourCauchyDirectionalDerivative data first density).val.1 target +
      (contourCauchyDirectionalDerivative data second density).val.1 target
  rw [contourCauchyDirectionalDerivative_value data (first + second) density small,
    contourCauchyDirectionalDerivative_value data first density small,
    contourCauchyDirectionalDerivative_value data second density small,
    ← intervalIntegral.integral_add
      (contourCauchyKernelVariation_density_integrable data first density (small.trans_le (min_le_right _ _)) target)
      (contourCauchyKernelVariation_density_integrable data second density (small.trans_le (min_le_right _ _)) target)]
  apply intervalIntegral.integral_congr
  intro source _
  unfold contourCauchyKernelVariation
  change (density.val.1 source - density.val.1 target) *
    ((first.val.2.val.1 source + second.val.2.val.1 source) / _ - _ *
      (first.val.1 target + second.val.1 target - (first.val.1 source + second.val.1 source)) / _) = _
  ring

theorem contourCauchyDirectionalDerivative_smul (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℂ) :
    contourCauchyDirectionalDerivative data (scalar • direction) density =
      scalar • contourCauchyDirectionalDerivative data direction density := by
  apply PeriodicHolderHalf.ext_value
  intro target
  change (contourCauchyDirectionalDerivative data (scalar • direction) density).val.1 target =
    scalar * (contourCauchyDirectionalDerivative data direction density).val.1 target
  rw [contourCauchyDirectionalDerivative_value data (scalar • direction) density small,
    contourCauchyDirectionalDerivative_value data direction density small,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro source _
  unfold contourCauchyKernelVariation
  simp only [complexC1Holder_smul_value, complexC1Holder_smul_tangent]
  ring

theorem contourCauchyDirectionalDerivative_norm_bound (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    ‖contourCauchyDirectionalDerivative data direction density‖ ≤
      (contourCauchyParameterOperatorConstant radius * ‖density‖) * ‖direction‖ := by
  have radius_nonnegative : 0 ≤ radius := (norm_nonneg _).trans near.le
  have operator_nonnegative : 0 ≤ contourCauchyParameterOperatorConstant radius :=
    (contourCauchyParameterSupConstant_nonneg radius_nonnegative small).trans (le_max_left _ _)
  apply norm_deriv_le_of_lip' (mul_nonneg (mul_nonneg operator_nonnegative (norm_nonneg _)) (norm_nonneg _))
  have positive : 0 < (radius - ‖data - standardCircleBanach‖) / (‖direction‖ + 1) :=
    div_pos (sub_pos.mpr near) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) positive] with parameter member
  have nearby := complexContourPerturbation_near data direction near
    (by simpa only [Metric.mem_ball, dist_zero_right] using member)
  simp only [zero_smul, add_zero, sub_zero]
  rw [extendedContourCauchy_eq _ _ (nearby.trans small), extendedContourCauchy_eq _ _ (near.trans small)]
  have bound := contourCauchyOperator_parameter_norm_bound (data + parameter • direction) data density
    radius_nonnegative small nearby.le near.le
  have identity : data + parameter • direction - data = parameter • direction := by abel
  rw [identity, norm_smul parameter direction] at bound
  exact bound.trans_eq (by ring)

def contourCauchyDerivativeCLM (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) : PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf :=
  LinearMap.mkContinuous
    ({ toFun := fun direction : PeriodicC1HolderHalf => contourCauchyDirectionalDerivative data direction density
       map_add' := fun first second => contourCauchyDirectionalDerivative_add data first second density (near.trans small)
       map_smul' := fun scalar direction => contourCauchyDirectionalDerivative_smul data direction density (near.trans small) scalar } :
      PeriodicC1HolderHalf →ₗ[ℂ] PeriodicHolderHalf)
    (contourCauchyParameterOperatorConstant radius * ‖density‖)
    (fun direction => contourCauchyDirectionalDerivative_norm_bound data direction density near small)

end

end EulerNonuniqueness.Paper
