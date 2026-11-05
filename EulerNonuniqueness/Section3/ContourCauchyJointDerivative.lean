import EulerNonuniqueness.Section3.ContourCauchyFrechet
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance jointCauchyHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance jointCauchyC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def contourCauchyJointDerivativeCLM (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    (PeriodicC1HolderHalf × PeriodicHolderHalf) →L[ℝ] PeriodicHolderHalf :=
  ((contourCauchyDerivativeCLM data density near small).restrictScalars ℝ).comp
    (ContinuousLinearMap.fst ℝ PeriodicC1HolderHalf PeriodicHolderHalf) +
  (contourCauchyOperatorCLM data (near.trans small)).comp
    (ContinuousLinearMap.snd ℝ PeriodicC1HolderHalf PeriodicHolderHalf)

theorem extendedContourCauchy_add_density (data : PeriodicC1HolderHalf) (first second : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    extendedContourCauchy data (first + second) = extendedContourCauchy data first + extendedContourCauchy data second := by
  rw [extendedContourCauchy_eq _ _ small, extendedContourCauchy_eq _ first small,
    extendedContourCauchy_eq _ second small, contourCauchyOperator_add]

theorem contourCauchy_joint_quadratic_remainder_bound (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (increment : PeriodicC1HolderHalf × PeriodicHolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius) (small : radius < min 1 (2 / (3 * Real.pi)))
    (increment_small : ‖increment‖ ≤ (radius - ‖data - standardCircleBanach‖) / 4) :
    ‖extendedContourCauchy (data + increment.1) (density + increment.2) - extendedContourCauchy data density -
      contourCauchyJointDerivativeCLM data density near small increment‖ ≤
      (8 * (contourCauchyUniformOperatorConstant radius * ‖density‖) /
        (radius - ‖data - standardCircleBanach‖) ^ 2 + contourCauchyParameterOperatorConstant radius) * ‖increment‖ ^ 2 := by
  have first_bound : ‖increment.1‖ ≤ ‖increment‖ := norm_fst_le increment
  have second_bound : ‖increment.2‖ ≤ ‖increment‖ := norm_snd_le increment
  have first_small := first_bound.trans increment_small
  have nonnegative : 0 ≤ radius := (norm_nonneg _).trans near.le
  have nearby : ‖data + increment.1 - standardCircleBanach‖ ≤ radius := by
    have identity : data + increment.1 - standardCircleBanach = (data - standardCircleBanach) + increment.1 := by abel
    rw [identity]
    exact (norm_add_le (data - standardCircleBanach) increment.1).trans (by linarith)
  have nearby_small := nearby.trans_lt small
  have remainder := contourCauchy_quadratic_remainder_bound data increment.1 density near small first_small
  have mixed : ‖extendedContourCauchy (data + increment.1) increment.2 - extendedContourCauchy data increment.2‖ ≤
      contourCauchyParameterOperatorConstant radius * ‖increment.1‖ * ‖increment.2‖ := by
    rw [extendedContourCauchy_eq _ _ nearby_small, extendedContourCauchy_eq _ _ (near.trans small)]
    have actual := contourCauchyOperator_parameter_norm_bound (data + increment.1) data increment.2
      nonnegative small nearby near.le
    have identity : data + increment.1 - data = increment.1 := by abel
    rwa [identity] at actual
  have identity : extendedContourCauchy (data + increment.1) (density + increment.2) - extendedContourCauchy data density -
      contourCauchyJointDerivativeCLM data density near small increment =
      (extendedContourCauchy (data + increment.1) density - extendedContourCauchy data density -
        contourCauchyDirectionalDerivative data increment.1 density) +
      (extendedContourCauchy (data + increment.1) increment.2 - extendedContourCauchy data increment.2) := by
    rw [extendedContourCauchy_add_density _ _ _ nearby_small, extendedContourCauchy_eq data increment.2 (near.trans small)]
    change _ - _ - (contourCauchyDirectionalDerivative data increment.1 density +
      contourCauchyOperator data (near.trans small) increment.2) = _
    abel
  rw [identity]
  apply (norm_add_le _ _).trans
  apply (add_le_add remainder mixed).trans
  have uniform_nonnegative := contourCauchyUniformOperatorConstant_nonneg nonnegative small
  have parameter_nonnegative := contourCauchyParameterOperatorConstant_nonneg nonnegative small
  have first_square : ‖increment.1‖ ^ 2 ≤ ‖increment‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg increment.1) (norm_nonneg increment)).mpr first_bound
  have mixed_product : ‖increment.1‖ * ‖increment.2‖ ≤ ‖increment‖ ^ 2 := by
    simpa only [pow_two] using mul_le_mul first_bound second_bound (norm_nonneg increment.2) (norm_nonneg increment)
  calc
    _ ≤ (8 * (contourCauchyUniformOperatorConstant radius * ‖density‖) /
        (radius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 2 +
        contourCauchyParameterOperatorConstant radius * ‖increment‖ ^ 2 := by
      apply add_le_add (mul_le_mul_of_nonneg_left first_square (by positivity))
      convert mul_le_mul_of_nonneg_left mixed_product parameter_nonnegative using 1 <;> ring
    _ = _ := by ring

theorem hasFDerivAt_contourCauchy_joint (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    HasFDerivAt (fun pair : PeriodicC1HolderHalf × PeriodicHolderHalf => extendedContourCauchy pair.1 pair.2)
      (contourCauchyJointDerivativeCLM data density near small) (data, density) := by
  apply (hasFDerivAt_iff_isLittleO_nhds_zero (𝕜 := ℝ)
    (f := fun pair : PeriodicC1HolderHalf × PeriodicHolderHalf => extendedContourCauchy pair.1 pair.2)
    (f' := contourCauchyJointDerivativeCLM data density near small) (x := (data, density))).mpr
  have remainder : (fun increment : PeriodicC1HolderHalf × PeriodicHolderHalf =>
      extendedContourCauchy (data + increment.1) (density + increment.2) - extendedContourCauchy data density -
        contourCauchyJointDerivativeCLM data density near small increment) =O[𝓝 0]
      (fun increment : PeriodicC1HolderHalf × PeriodicHolderHalf => ‖increment‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound
      (8 * (contourCauchyUniformOperatorConstant radius * ‖density‖) /
        (radius - ‖data - standardCircleBanach‖) ^ 2 + contourCauchyParameterOperatorConstant radius)
    have positive : 0 < (radius - ‖data - standardCircleBanach‖) / 4 := by linarith
    filter_upwards [Metric.ball_mem_nhds (0 : PeriodicC1HolderHalf × PeriodicHolderHalf) positive] with increment member
    have increment_small : ‖increment‖ ≤ (radius - ‖data - standardCircleBanach‖) / 4 := by
      have norm_small : ‖increment‖ < (radius - ‖data - standardCircleBanach‖) / 4 := by
        simpa only [mem_ball, dist_zero_right] using member
      exact norm_small.le
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖increment‖)] using
      contourCauchy_joint_quadratic_remainder_bound data density increment near small increment_small
  exact remainder.trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := PeriodicC1HolderHalf × PeriodicHolderHalf) (by decide : 1 < (2 : ℕ)))

end

end EulerNonuniqueness.Paper
