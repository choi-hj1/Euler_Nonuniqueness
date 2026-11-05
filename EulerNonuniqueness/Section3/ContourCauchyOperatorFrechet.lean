import EulerNonuniqueness.Section3.ContourFirstVariationBilinear

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance cauchyOperatorFrechetHolderSpace : NormedSpace ℂ PeriodicHolderHalf := Submodule.normedSpace complexPeriodicHolderGraph
local instance cauchyOperatorFrechetC1Space : NormedSpace ℂ PeriodicC1HolderHalf := Submodule.normedSpace complexPeriodicC1HolderGraph
local instance cauchyOperatorFrechetOperatorGroup : NormedAddCommGroup (PeriodicHolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance cauchyOperatorFrechetOperatorSpace : NormedSpace ℂ (PeriodicHolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)

theorem contourCauchyOperator_complex_smul (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (scalar : ℂ) (density : PeriodicHolderHalf) :
    contourCauchyOperator data small (scalar • density) = scalar • contourCauchyOperator data small density := by
  apply PeriodicHolderHalf.ext_value
  intro target
  change contourCauchyTransform data.val.1 data.val.2.val.1 (scalar • density).val.1 target =
    scalar * contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 target
  have identity : contourCauchyDensityRemainder data.val.1 data.val.2.val.1 (scalar • density).val.1 target =
      (fun source => scalar * contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 target source) := by
    funext source
    change ((scalar * density.val.1 source) - (scalar * density.val.1 target)) * _ / _ = _
    unfold contourCauchyDensityRemainder
    ring
  unfold contourCauchyTransform
  rw [identity, intervalIntegral.integral_const_mul]
  change scalar * _ - (Real.pi : ℂ) * Complex.I * (scalar * density.val.1 target) = scalar * _
  ring

def contourCauchyOperatorCCLM (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    PeriodicHolderHalf →L[ℂ] PeriodicHolderHalf :=
  LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf)
    ({ toFun := contourCauchyOperator data small
       map_add' := contourCauchyOperator_add data small
       map_smul' := contourCauchyOperator_complex_smul data small } : PeriodicHolderHalf →ₗ[ℂ] PeriodicHolderHalf)
    (max (contourCauchySupConstant data) (contourCauchyGlobalHolderConstant data))
    (contourCauchyOperator_norm_bound data small)

def extendedContourCauchyOperatorCLM (data : PeriodicC1HolderHalf) : PeriodicHolderHalf →L[ℂ] PeriodicHolderHalf :=
  if small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) then contourCauchyOperatorCCLM data small else 0

theorem extendedContourCauchyOperatorCLM_apply (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf) :
    extendedContourCauchyOperatorCLM data density = extendedContourCauchy data density := by
  classical
  by_cases small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))
  · simp only [extendedContourCauchyOperatorCLM, dif_pos small, extendedContourCauchy_eq data density small]
    rfl
  · simp only [extendedContourCauchyOperatorCLM, dif_neg small, extendedContourCauchy, ContinuousLinearMap.zero_apply]

theorem contourCauchyOperatorCLM_remainder_bound (data increment : PeriodicC1HolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi)))
    (increment_small : ‖increment‖ ≤ (radius - ‖data - standardCircleBanach‖) / 4) :
    ‖extendedContourCauchyOperatorCLM (data + increment) - extendedContourCauchyOperatorCLM data -
      contourCauchyFirstVariationCLM data near small increment‖ ≤
      (8 * contourCauchyUniformOperatorConstant radius /
        (radius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 2 := by
  have operator_nonnegative := contourCauchyUniformOperatorConstant_nonneg ((norm_nonneg _).trans near.le) small
  apply ContinuousLinearMap.opNorm_le_bound (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := PeriodicHolderHalf) (F := PeriodicHolderHalf)
    (extendedContourCauchyOperatorCLM (data + increment) - extendedContourCauchyOperatorCLM data -
      contourCauchyFirstVariationCLM data near small increment)
    (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) operator_nonnegative) (sq_nonneg _)) (sq_nonneg _))
  intro density
  rw [ContinuousLinearMap.sub_apply (R := ℂ) (R₂ := ℂ) (M := PeriodicHolderHalf) (M₂ := PeriodicHolderHalf),
    ContinuousLinearMap.sub_apply (R := ℂ) (R₂ := ℂ) (M := PeriodicHolderHalf) (M₂ := PeriodicHolderHalf),
    extendedContourCauchyOperatorCLM_apply, extendedContourCauchyOperatorCLM_apply,
    contourCauchyFirstVariationCLM_apply]
  exact (contourCauchy_quadratic_remainder_bound data increment density near small increment_small).trans_eq (by ring)

theorem hasFDerivAt_extendedContourCauchyOperatorCLM (data : PeriodicC1HolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    HasFDerivAt extendedContourCauchyOperatorCLM (contourCauchyFirstVariationCLM data near small) data := by
  apply (hasFDerivAt_iff_isLittleO_nhds_zero (𝕜 := ℂ)
    (f := extendedContourCauchyOperatorCLM) (f' := contourCauchyFirstVariationCLM data near small) (x := data)).mpr
  have remainder_bound : (fun increment : PeriodicC1HolderHalf =>
      extendedContourCauchyOperatorCLM (data + increment) - extendedContourCauchyOperatorCLM data -
        contourCauchyFirstVariationCLM data near small increment) =O[𝓝 0]
      (fun increment : PeriodicC1HolderHalf => ‖increment‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound (8 * contourCauchyUniformOperatorConstant radius /
      (radius - ‖data - standardCircleBanach‖) ^ 2)
    have positive : 0 < (radius - ‖data - standardCircleBanach‖) / 4 := by linarith
    filter_upwards [Metric.ball_mem_nhds (0 : PeriodicC1HolderHalf) positive] with increment member
    have increment_small : ‖increment‖ ≤ (radius - ‖data - standardCircleBanach‖) / 4 :=
      (show ‖increment‖ < _ from by simpa only [mem_ball, dist_zero_right] using member).le
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖increment‖)] using
      contourCauchyOperatorCLM_remainder_bound data increment near small increment_small
  exact remainder_bound.trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := PeriodicC1HolderHalf) (by decide : 1 < (2 : ℕ)))

end

end EulerNonuniqueness.Paper
