import EulerNonuniqueness.Section3.C1HolderBanachAlgebra
import EulerNonuniqueness.Section3.ComplexHolderInstances
import EulerNonuniqueness.Section3.ContourCentroidGaugePointBounds
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance spatialCompositionRealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance spatialCompositionDerivativeGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℂ) (σ₁₂ := RingHom.id ℝ)

private theorem spatial_c1_complex_norm_smul (scalar : ℂ) (data : PeriodicC1HolderHalf) :
    ‖scalar • data‖ = ‖scalar‖ * ‖data‖ := by
  change ‖scalar • data.val‖ = _
  exact norm_smul scalar data.val

structure SpatialContourField (center : ℂ) (radius : ℝ) where
  field : ℂ → ℂ
  derivative : ℂ → ℂ →L[ℝ] ℂ
  strain : ℝ≥0
  hessian : ℝ≥0
  hasFDerivAt : ∀ position ∈ Metric.closedBall center (3 * radius),
    HasFDerivAt field (derivative position) position
  derivative_bound : ∀ position ∈ Metric.closedBall center (3 * radius), ‖derivative position‖ ≤ strain
  derivative_lipschitz : LipschitzOnWith hessian derivative (Metric.closedBall center (3 * radius))

namespace SpatialContourField

variable {center : ℂ} {radius : ℝ}

def position (data : PeriodicC1HolderHalf) (label : ℝ) : ℂ := center + radius • data.val.1 label

theorem position_mem (data : PeriodicC1HolderHalf) (radiusPositive : 0 < radius)
    (bound : ‖data‖ ≤ 3) (label : ℝ) : position (center := center) (radius := radius) data label ∈
      Metric.closedBall center (3 * radius) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  simp only [position, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos radiusPositive]
  exact (mul_le_mul_of_nonneg_left ((PeriodicC1HolderHalf.value_bound data label).trans bound)
    radiusPositive.le).trans_eq (mul_comm _ _)

def value (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf) (label : ℝ) : ℂ :=
  radius⁻¹ • (source.field (position (center := center) (radius := radius) data label) - source.field center)

def tangent (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf) (label : ℝ) : ℂ :=
  source.derivative (position (center := center) (radius := radius) data label) (data.val.2.val.1 label)

theorem value_hasDerivAt (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf)
    (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3) (label : ℝ) :
    HasDerivAt (source.value data) (source.tangent data label) label := by
  have positionDerivative : HasDerivAt (position (center := center) (radius := radius) data)
      (radius • data.val.2.val.1 label) label :=
    ((PeriodicC1HolderHalf.hasDerivAt data label).const_smul radius).const_add center
  have composed := (source.hasFDerivAt _ (position_mem data radiusPositive bound label)).comp_hasDerivAt
    label positionDerivative
  have normalized := (composed.sub_const (source.field center)).const_smul radius⁻¹
  simpa only [value, tangent, Function.comp_def, map_smul, smul_smul,
    inv_mul_cancel₀ radiusPositive.ne', one_smul] using normalized

theorem tangent_continuous (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf)
    (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3) : Continuous (source.tangent data) := by
  have positionContinuous : Continuous (position (center := center) (radius := radius) data) :=
    continuous_const.add (continuous_const.smul data.val.1.continuous)
  have derivativeContinuous := source.derivative_lipschitz.continuousOn.comp_continuous
    positionContinuous (position_mem data radiusPositive bound)
  exact derivativeContinuous.clm_apply data.val.2.val.1.continuous

theorem value_bound (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf)
    (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3) (label : ℝ) :
    ‖source.value data label‖ ≤ 3 * (source.strain : ℝ) := by
  have centerInside : center ∈ Metric.closedBall center (3 * radius) := Metric.mem_closedBall_self (by positivity)
  have estimate := (convex_closedBall center (3 * radius)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun position member => (source.hasFDerivAt position member).hasFDerivWithinAt)
    source.derivative_bound centerInside (position_mem data radiusPositive bound label)
  have positionBound : ‖position (center := center) (radius := radius) data label - center‖ ≤ radius * 3 := by
    simpa only [position, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos radiusPositive] using
      mul_le_mul_of_nonneg_left ((PeriodicC1HolderHalf.value_bound data label).trans bound) radiusPositive.le
  have combined := estimate.trans (mul_le_mul_of_nonneg_left positionBound source.strain.coe_nonneg)
  rw [value, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr radiusPositive)]
  have scaled := mul_le_mul_of_nonneg_left combined (inv_nonneg.mpr radiusPositive.le)
  convert scaled using 1
  field_simp
  ring

theorem tangent_bound (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf)
    (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3) (label : ℝ) :
    ‖source.tangent data label‖ ≤ 3 * (source.strain : ℝ) := by
  exact ((source.derivative _).le_opNorm _).trans
    ((mul_le_mul (source.derivative_bound _ (position_mem data radiusPositive bound label))
      ((PeriodicC1HolderHalf.speed_bound data label).trans bound) (norm_nonneg _) source.strain.coe_nonneg).trans_eq (mul_comm _ _))

theorem tangent_holder_bound (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf)
    (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3) (first second : ℝ) :
    ‖source.tangent data first - source.tangent data second‖ ≤
      (3 * (source.strain : ℝ) + 18 * radius * (source.hessian : ℝ)) * Real.sqrt |first - second| := by
  let firstPosition := position (center := center) (radius := radius) data first
  let secondPosition := position (center := center) (radius := radius) data second
  have derivativeDifference : ‖source.derivative firstPosition - source.derivative secondPosition‖ ≤
      (source.hessian : ℝ) * (radius * (6 * Real.sqrt |first - second|)) := by
    have estimate := source.derivative_lipschitz.norm_sub_le
      (position_mem data radiusPositive bound first) (position_mem data radiusPositive bound second)
    have positionDifference : ‖firstPosition - secondPosition‖ ≤ radius * (6 * Real.sqrt |first - second|) := by
      dsimp only [firstPosition, secondPosition, position]
      rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos radiusPositive]
      exact mul_le_mul_of_nonneg_left ((PeriodicC1HolderHalf.value_holder_bound data first second).trans
        (mul_le_mul_of_nonneg_right (show 2 * ‖data‖ ≤ 6 by linarith)
          (Real.sqrt_nonneg _))) radiusPositive.le
    exact estimate.trans (mul_le_mul_of_nonneg_left positionDifference source.hessian.coe_nonneg)
  have tangentDifference := (PeriodicC1HolderHalf.derivative_holder_bound data first second).trans
    (mul_le_mul_of_nonneg_right bound (Real.sqrt_nonneg _))
  have decomposition : source.tangent data first - source.tangent data second =
      source.derivative firstPosition (data.val.2.val.1 first - data.val.2.val.1 second) +
        (source.derivative firstPosition - source.derivative secondPosition) (data.val.2.val.1 second) := by
    simp only [tangent, firstPosition, secondPosition, map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [decomposition]
  have firstBound := ((source.derivative firstPosition).le_opNorm _).trans
    (mul_le_mul (source.derivative_bound _ (position_mem data radiusPositive bound first)) tangentDifference
      (norm_nonneg _) source.strain.coe_nonneg)
  have secondBound := ((source.derivative firstPosition - source.derivative secondPosition).le_opNorm _).trans
    (mul_le_mul derivativeDifference ((PeriodicC1HolderHalf.speed_bound data second).trans bound)
      (norm_nonneg _) (by positivity))
  exact (norm_add_le _ _).trans ((add_le_add firstBound secondBound).trans_eq (by ring))

def compose (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf)
    (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3) : PeriodicC1HolderHalf :=
  PeriodicC1HolderHalf.ofFunctions (source.value data) (source.tangent data)
    (continuous_iff_continuousAt.mpr (fun label => (source.value_hasDerivAt data radiusPositive bound label).continuousAt))
    (source.tangent_continuous data radiusPositive bound)
    (3 * source.strain) (3 * source.strain) (3 * source.strain + 18 * radius * source.hessian)
    (source.value_bound data radiusPositive bound) (source.tangent_bound data radiusPositive bound)
    (source.tangent_holder_bound data radiusPositive bound) (source.value_hasDerivAt data radiusPositive bound)
    (fun label => by dsimp only [value, position]; rw [PeriodicC1HolderHalf.periodic data label])
    (fun label => by dsimp only [tangent, position]; rw [PeriodicC1HolderHalf.periodic data label,
      PeriodicHolderHalf.periodic data.val.2 label])

theorem compose_norm_bound (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf)
    (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3) :
    ‖source.compose data radiusPositive bound‖ ≤ 3 * (source.strain : ℝ) + 18 * radius * (source.hessian : ℝ) := by
  apply (PeriodicC1HolderHalf.ofFunctions_norm_bound _ _ _ _ (by positivity) (by positivity) (by positivity)
    _ _ _ _ _ _).trans
  exact max_le (le_add_of_nonneg_right (by positivity))
    (max_le (le_add_of_nonneg_right (by positivity)) le_rfl)

theorem compose_value (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf)
    (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3) (label : ℝ) :
    (source.compose data radiusPositive bound).val.1 label = source.value data label := rfl

theorem compose_tangent (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf)
    (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3) (label : ℝ) :
    (source.compose data radiusPositive bound).val.2.val.1 label = source.tangent data label := rfl

def rotatedCompose (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf)
    (phase : Circle) (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3) : PeriodicC1HolderHalf :=
  (phase : ℂ)⁻¹ • source.compose ((phase : ℂ) • data) radiusPositive
    (by simpa only [spatial_c1_complex_norm_smul, Circle.norm_coe, one_mul] using bound)

theorem rotatedCompose_value (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf)
    (phase : Circle) (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3) (label : ℝ) :
    (source.rotatedCompose data phase radiusPositive bound).val.1 label =
      radius⁻¹ • ((phase : ℂ)⁻¹ *
        (source.field (center + radius • ((phase : ℂ) * data.val.1 label)) - source.field center)) := by
  simp only [rotatedCompose, complexC1Holder_smul_value, compose_value, value, position,
    Complex.real_smul]
  ring

theorem rotatedCompose_tangent (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf)
    (phase : Circle) (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3) (label : ℝ) :
    (source.rotatedCompose data phase radiusPositive bound).val.2.val.1 label =
      (phase : ℂ)⁻¹ * source.derivative
        (center + radius • ((phase : ℂ) * data.val.1 label)) ((phase : ℂ) * data.val.2.val.1 label) := rfl

theorem rotatedCompose_norm_bound (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf)
    (phase : Circle) (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3) :
    ‖source.rotatedCompose data phase radiusPositive bound‖ ≤
      3 * (source.strain : ℝ) + 18 * radius * (source.hessian : ℝ) := by
  rw [rotatedCompose, spatial_c1_complex_norm_smul, norm_inv, Circle.norm_coe, inv_one, one_mul]
  exact source.compose_norm_bound _ radiusPositive _

def rawRotatedCompose (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf)
    (phase : Circle) (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3) : PeriodicC1HolderHalf :=
  source.rotatedCompose data phase radiusPositive bound +
    c1Constant (radius⁻¹ • ((phase : ℂ)⁻¹ * source.field center))

theorem rawRotatedCompose_value (source : SpatialContourField center radius) (data : PeriodicC1HolderHalf)
    (phase : Circle) (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3) (label : ℝ) :
    (source.rawRotatedCompose data phase radiusPositive bound).val.1 label =
      radius⁻¹ • ((phase : ℂ)⁻¹ * source.field (center + radius • ((phase : ℂ) * data.val.1 label))) := by
  change (source.rotatedCompose data phase radiusPositive bound).val.1 label +
    radius⁻¹ • ((phase : ℂ)⁻¹ * source.field center) = _
  rw [source.rotatedCompose_value]
  simp only [Complex.real_smul]
  ring

theorem gaugeProjection_rawRotatedCompose (source : SpatialContourField center radius)
    (data : PeriodicC1HolderHalf) (phase : Circle) (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    contourCentroidGaugeProjection data (source.rawRotatedCompose data phase radiusPositive bound) =
      contourCentroidGaugeProjection data (source.rotatedCompose data phase radiusPositive bound) := by
  let constant := radius⁻¹ • ((phase : ℂ)⁻¹ * source.field center)
  have derivativeConstant := DFunLike.congr_fun (contourCentroidFunctional_derivative_constant data small) constant
  change (fderiv ℝ contourCentroidFunctional data) (c1Constant constant) = constant at derivativeConstant
  have annihilation : contourCentroidGaugeProjection data (c1Constant constant) = 0 := by
    rw [contourCentroidGaugeProjection_apply, derivativeConstant]
    exact sub_self (c1Constant constant)
  change contourCentroidGaugeProjection data
    (source.rotatedCompose data phase radiusPositive bound + c1Constant constant) = _
  rw [map_add, annihilation, add_zero]

theorem gaugeProjection_rawRotatedCompose_norm_bound (source : SpatialContourField center radius)
    (data : PeriodicC1HolderHalf) (phase : Circle) (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) {constant : ℝ} (constantNonnegative : 0 ≤ constant)
    (centroidDerivativeBound : ‖fderiv ℝ contourCentroidFunctional data‖ ≤ constant) :
    ‖contourCentroidGaugeProjection data (source.rawRotatedCompose data phase radiusPositive bound)‖ ≤
      (1 + constant) * (3 * (source.strain : ℝ) + 18 * radius * (source.hessian : ℝ)) := by
  rw [source.gaugeProjection_rawRotatedCompose data phase radiusPositive bound small]
  exact contourCentroidGaugeProjection_apply_norm_bound _ _ constantNonnegative centroidDerivativeBound
    (source.rotatedCompose_norm_bound data phase radiusPositive bound)

end SpatialContourField

end EulerNonuniqueness.Paper
