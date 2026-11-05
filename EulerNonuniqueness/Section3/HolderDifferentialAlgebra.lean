import EulerNonuniqueness.Section3.ContourVelocityHolderDerivative
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance differentialHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance differentialHolderOperatorGroup : SeminormedAddCommGroup (PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance differentialHolderOperatorRealSpace : NormedSpace ℝ (PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)

def holderProductRealBilinear : PeriodicHolderHalf →ₗ[ℝ] PeriodicHolderHalf →ₗ[ℝ] PeriodicHolderHalf where
  toFun first :=
    { toFun := fun second => holderProduct first second
      map_add' := fun second third => by
        apply PeriodicHolderHalf.ext_value
        intro label
        exact mul_add _ _ _
      map_smul' := fun scalar second => by
        apply PeriodicHolderHalf.ext_value
        intro label
        change first.val.1 label * (scalar • second.val.1 label) = scalar • (first.val.1 label * second.val.1 label)
        simp only [Complex.real_smul]
        ring }
  map_add' first second := by
    apply LinearMap.ext
    intro third
    apply PeriodicHolderHalf.ext_value
    intro label
    exact add_mul _ _ _
  map_smul' scalar first := by
    apply LinearMap.ext
    intro second
    apply PeriodicHolderHalf.ext_value
    intro label
    exact smul_mul_assoc scalar (first.val.1 label) (second.val.1 label)

def holderProductRealCLM : PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf :=
  LinearMap.mkContinuous₂ (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ)
    (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (G := PeriodicHolderHalf)
    holderProductRealBilinear 2 holderProduct_norm_bound

def UniformlyNonzeroHolder (data : PeriodicHolderHalf) : Prop :=
  ∃ lower : ℝ, 0 < lower ∧ ∀ label, lower ≤ ‖data.val.1 label‖

def extendedHolderInverse (data : PeriodicHolderHalf) : PeriodicHolderHalf := by
  classical
  exact if separated : UniformlyNonzeroHolder data then
    holderInverse data separated.choose_spec.1 separated.choose_spec.2 else 0

theorem extendedHolderInverse_eq (data : PeriodicHolderHalf) {lower : ℝ} (positive : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) :
    extendedHolderInverse data = holderInverse data positive separated := by
  classical
  have nonzero : UniformlyNonzeroHolder data := ⟨lower, positive, separated⟩
  rw [extendedHolderInverse, dif_pos nonzero]
  apply PeriodicHolderHalf.ext_value
  intro label
  rfl

theorem holder_perturbation_separated (data increment : PeriodicHolderHalf) {lower : ℝ}
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) (small : ‖increment‖ ≤ lower / 2) (label : ℝ) :
    lower / 2 ≤ ‖(data + increment).val.1 label‖ := by
  have triangle := norm_add_le (data.val.1 label + increment.val.1 label) (-increment.val.1 label)
  rw [add_neg_cancel_right, norm_neg] at triangle
  change lower / 2 ≤ ‖data.val.1 label + increment.val.1 label‖
  linarith [separated label, PeriodicHolderHalf.value_bound increment label]

def holderInverseDerivativeCLM (data : PeriodicHolderHalf) : PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf :=
  -((holderProductRealCLM (extendedHolderInverse data)).comp
    (holderProductRealCLM.flip (extendedHolderInverse data)))

theorem holderInverse_remainder_identity (data increment : PeriodicHolderHalf) {lower : ℝ}
    (positive : 0 < lower) (separated : ∀ label, lower ≤ ‖data.val.1 label‖)
    (small : ‖increment‖ ≤ lower / 2) :
    extendedHolderInverse (data + increment) - extendedHolderInverse data - holderInverseDerivativeCLM data increment =
      holderProduct increment (holderProduct increment (holderProduct (extendedHolderInverse (data + increment))
        (holderProduct (extendedHolderInverse data) (extendedHolderInverse data)))) := by
  have next_separated := holder_perturbation_separated data increment separated small
  have half_positive : 0 < lower / 2 := by linarith
  have derivative_apply : holderInverseDerivativeCLM data increment =
      -holderProduct (extendedHolderInverse data) (holderProduct increment (extendedHolderInverse data)) := rfl
  rw [derivative_apply, extendedHolderInverse_eq data positive separated,
    extendedHolderInverse_eq (data + increment) half_positive next_separated]
  apply PeriodicHolderHalf.ext_value
  intro label
  have first_ne := norm_ne_zero_iff.mp (ne_of_gt (positive.trans_le (separated label)))
  have second_ne := norm_ne_zero_iff.mp (ne_of_gt (half_positive.trans_le (next_separated label)))
  change data.val.1 label + increment.val.1 label ≠ 0 at second_ne
  change (data.val.1 label + increment.val.1 label)⁻¹ - (data.val.1 label)⁻¹ -
      (-((data.val.1 label)⁻¹ * (increment.val.1 label * (data.val.1 label)⁻¹))) =
    increment.val.1 label * (increment.val.1 label * ((data.val.1 label + increment.val.1 label)⁻¹ *
      ((data.val.1 label)⁻¹ * (data.val.1 label)⁻¹)))
  field_simp
  ring

theorem holderInverse_remainder_norm (data increment : PeriodicHolderHalf) {lower bound : ℝ}
    (positive : 0 < lower) (separated : ∀ label, lower ≤ ‖data.val.1 label‖)
    (small : ‖increment‖ ≤ lower / 2) (bound_nonnegative : 0 ≤ bound)
    (first_bound : ‖extendedHolderInverse data‖ ≤ bound)
    (second_bound : ‖extendedHolderInverse (data + increment)‖ ≤ bound) :
    ‖extendedHolderInverse (data + increment) - extendedHolderInverse data - holderInverseDerivativeCLM data increment‖ ≤
      (16 * bound ^ 3) * ‖increment‖ ^ 2 := by
  rw [holderInverse_remainder_identity data increment positive separated small]
  calc
    _ ≤ 2 * ‖increment‖ * ‖holderProduct increment (holderProduct (extendedHolderInverse (data + increment))
        (holderProduct (extendedHolderInverse data) (extendedHolderInverse data)))‖ := holderProduct_norm_bound _ _
    _ ≤ 2 * ‖increment‖ * (2 * ‖increment‖ * (2 * ‖extendedHolderInverse (data + increment)‖ *
        (2 * ‖extendedHolderInverse data‖ * ‖extendedHolderInverse data‖))) := by
      gcongr
      apply (holderProduct_norm_bound _ _).trans
      gcongr
      apply (holderProduct_norm_bound _ _).trans
      gcongr
      exact holderProduct_norm_bound _ _
    _ ≤ 2 * ‖increment‖ * (2 * ‖increment‖ * (2 * bound * (2 * bound * bound))) := by gcongr
    _ = _ := by ring

theorem extendedHolderInverse_norm_bound (data : PeriodicHolderHalf) {lower : ℝ}
    (positive : 0 < lower) (separated : ∀ label, lower ≤ ‖data.val.1 label‖) :
    ‖extendedHolderInverse data‖ ≤ max (1 / lower) (‖data‖ / lower ^ 2) := by
  rw [extendedHolderInverse_eq data positive separated]
  exact holderInverse_norm_bound data positive separated

theorem hasFDerivAt_extendedHolderInverse (data : PeriodicHolderHalf) {lower : ℝ}
    (positive : 0 < lower) (separated : ∀ label, lower ≤ ‖data.val.1 label‖) :
    HasFDerivAt extendedHolderInverse (holderInverseDerivativeCLM data) data := by
  apply (hasFDerivAt_iff_isLittleO_nhds_zero (𝕜 := ℝ) (f := extendedHolderInverse)
    (f' := holderInverseDerivativeCLM data) (x := data)).mpr
  let bound := max (1 / (lower / 2)) ((‖data‖ + lower / 2) / (lower / 2) ^ 2)
  have half_positive : 0 < lower / 2 := by linarith
  have bound_nonnegative : 0 ≤ bound := (by positivity : (0 : ℝ) ≤ 1 / (lower / 2)).trans (le_max_left _ _)
  have first_bound : ‖extendedHolderInverse data‖ ≤ bound := by
    have half_separated : ∀ label, lower / 2 ≤ ‖data.val.1 label‖ := fun label => by linarith [separated label]
    apply (extendedHolderInverse_norm_bound data half_positive half_separated).trans
    apply max_le_max le_rfl
    exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  have remainder : (fun increment : PeriodicHolderHalf => extendedHolderInverse (data + increment) -
      extendedHolderInverse data - holderInverseDerivativeCLM data increment) =O[𝓝 0]
      (fun increment : PeriodicHolderHalf => ‖increment‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound (16 * bound ^ 3)
    filter_upwards [Metric.ball_mem_nhds (0 : PeriodicHolderHalf) half_positive] with increment member
    have increment_small : ‖increment‖ ≤ lower / 2 := by
      have strict : ‖increment‖ < lower / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using member
      exact strict.le
    have next_separated := holder_perturbation_separated data increment separated increment_small
    have second_bound : ‖extendedHolderInverse (data + increment)‖ ≤ bound := by
      apply (extendedHolderInverse_norm_bound (data + increment) half_positive next_separated).trans
      apply max_le_max le_rfl
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact (norm_add_le data increment).trans (add_le_add_left increment_small _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖increment‖)] using
      holderInverse_remainder_norm data increment positive separated increment_small bound_nonnegative first_bound second_bound
  exact remainder.trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := PeriodicHolderHalf) (by decide : 1 < (2 : ℕ)))

end

end EulerNonuniqueness.Paper
