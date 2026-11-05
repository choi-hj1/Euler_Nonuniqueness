import EulerNonuniqueness.Section3.ContourSecondVariationBilinear
import EulerNonuniqueness.Section3.ContourDerivativeQuadraticRemainder

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance secondFrechetHolderComplexSpace : NormedSpace ℂ PeriodicHolderHalf :=
  Submodule.normedSpace complexPeriodicHolderGraph
local instance secondFrechetC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf :=
  Submodule.normedSpace complexPeriodicC1HolderGraph
local instance secondFrechetOperatorGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance secondFrechetOperatorSpace : NormedSpace ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)

theorem secondFrechet_firstDerivative_apply (data direction : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    contourCauchyDerivativeCLM data density near small direction =
      contourCauchyDirectionalDerivative data direction density := rfl

theorem contourCauchy_fderiv_quadratic_remainder_direction_bound
    (data increment direction : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (increment_small : ‖increment‖ ≤ (innerRadius - ‖data - standardCircleBanach‖) / 4) :
    ‖(fderiv ℂ (fun current => extendedContourCauchy current density) (data + increment) -
      fderiv ℂ (fun current => extendedContourCauchy current density) data -
      contourCauchySecondVariationCLM data density near gap small increment) direction‖ ≤
      (8 * contourCauchyParameterOperatorConstant outerRadius * ‖density‖ /
        (innerRadius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 2 * ‖direction‖ := by
  have perturbed_near : ‖data + increment - standardCircleBanach‖ < innerRadius := by
    have estimate : ‖data + increment - standardCircleBanach‖ ≤
        ‖data - standardCircleBanach‖ + ‖increment‖ := by
      convert norm_add_le (data - standardCircleBanach) increment using 1 <;> congr 1 <;> abel
    linarith
  have derivative (point : PeriodicC1HolderHalf) (point_near : ‖point - standardCircleBanach‖ < innerRadius) :
      fderiv ℂ (fun current => extendedContourCauchy current density) point =
        contourCauchyDerivativeCLM point density point_near (gap.trans small) :=
    HasFDerivAt.fderiv (𝕜 := ℂ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
      (hasFDerivAt_extendedContourCauchy point density point_near (gap.trans small))
  rw [derivative (data + increment) perturbed_near, derivative data near]
  rw [ContinuousLinearMap.sub_apply (R := ℂ) (R₂ := ℂ) (M := PeriodicC1HolderHalf) (M₂ := PeriodicHolderHalf),
    ContinuousLinearMap.sub_apply (R := ℂ) (R₂ := ℂ) (M := PeriodicC1HolderHalf) (M₂ := PeriodicHolderHalf),
    secondFrechet_firstDerivative_apply, secondFrechet_firstDerivative_apply,
    contourCauchySecondVariationCLM_apply]
  rw [contourCauchySecondVariation_symm data increment direction density (near.trans (gap.trans small))]
  exact (contourCauchyDerivative_quadratic_remainder_bound data direction increment density near gap small
    increment_small).trans_eq (by ring)

theorem contourCauchy_fderiv_quadratic_remainder_bound
    (data increment : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (increment_small : ‖increment‖ ≤ (innerRadius - ‖data - standardCircleBanach‖) / 4) :
    ‖fderiv ℂ (fun current => extendedContourCauchy current density) (data + increment) -
      fderiv ℂ (fun current => extendedContourCauchy current density) data -
      contourCauchySecondVariationCLM data density near gap small increment‖ ≤
      (8 * contourCauchyParameterOperatorConstant outerRadius * ‖density‖ /
        (innerRadius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 2 := by
  have parameter_nonnegative := contourCauchyParameterOperatorConstant_nonneg
    ((norm_nonneg _).trans (near.trans gap).le) small
  apply ContinuousLinearMap.opNorm_le_bound (𝕜 := ℂ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
    (fderiv ℂ (fun current => extendedContourCauchy current density) (data + increment) -
      fderiv ℂ (fun current => extendedContourCauchy current density) data -
      contourCauchySecondVariationCLM data density near gap small increment)
    (mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) parameter_nonnegative)
      (norm_nonneg density)) (sq_nonneg _)) (sq_nonneg _))
  intro direction
  exact contourCauchy_fderiv_quadratic_remainder_direction_bound data increment direction density near gap small increment_small

theorem hasFDerivAt_fderiv_extendedContourCauchy (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    HasFDerivAt (fun current => fderiv ℂ (fun point => extendedContourCauchy point density) current)
      (contourCauchySecondVariationCLM data density near gap small) data := by
  apply (hasFDerivAt_iff_isLittleO_nhds_zero (𝕜 := ℂ)
    (f := fun current => fderiv ℂ (fun point => extendedContourCauchy point density) current)
    (f' := contourCauchySecondVariationCLM data density near gap small) (x := data)).mpr
  have remainder_bound : (fun increment : PeriodicC1HolderHalf =>
      fderiv ℂ (fun current => extendedContourCauchy current density) (data + increment) -
        fderiv ℂ (fun current => extendedContourCauchy current density) data -
        contourCauchySecondVariationCLM data density near gap small increment) =O[𝓝 0]
      (fun increment : PeriodicC1HolderHalf => ‖increment‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound
      (8 * contourCauchyParameterOperatorConstant outerRadius * ‖density‖ /
        (innerRadius - ‖data - standardCircleBanach‖) ^ 2)
    have positive : 0 < (innerRadius - ‖data - standardCircleBanach‖) / 4 := by linarith
    filter_upwards [Metric.ball_mem_nhds (0 : PeriodicC1HolderHalf) positive] with increment member
    have increment_small : ‖increment‖ ≤ (innerRadius - ‖data - standardCircleBanach‖) / 4 := by
      exact (show ‖increment‖ < _ from by simpa only [mem_ball, dist_zero_right] using member).le
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖increment‖)] using
      contourCauchy_fderiv_quadratic_remainder_bound data increment density near gap small increment_small
  exact remainder_bound.trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := PeriodicC1HolderHalf) (by decide : 1 < (2 : ℕ)))

end

end EulerNonuniqueness.Paper
