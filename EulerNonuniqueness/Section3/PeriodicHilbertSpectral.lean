import EulerNonuniqueness.Section3.PeriodicHilbertProjections

open MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance spectralHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance spectralC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance spectralC1Module : Module ℂ PeriodicC1HolderHalf := Submodule.module complexPeriodicC1HolderGraph
local instance spectralC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf := complexC1HolderNormedSpace
local instance spectralC1BoundedSMul : IsBoundedSMul ℂ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℂ) (E := PeriodicC1HolderHalf)

theorem c1AngularIntegral_add (first second : PeriodicC1HolderHalf) :
    c1AngularIntegralCCLM (first + second) = c1AngularIntegralCCLM first + c1AngularIntegralCCLM second := by
  change (∫ label in (0 : ℝ)..(2 * Real.pi), first.val.1 label + second.val.1 label) = _
  exact intervalIntegral.integral_add (first.val.1.continuous.intervalIntegrable _ _)
    (second.val.1.continuous.intervalIntegrable _ _)

theorem c1AngularIntegral_sub (first second : PeriodicC1HolderHalf) :
    c1AngularIntegralCCLM (first - second) = c1AngularIntegralCCLM first - c1AngularIntegralCCLM second := by
  change (∫ label in (0 : ℝ)..(2 * Real.pi), first.val.1 label - second.val.1 label) = _
  exact intervalIntegral.integral_sub (first.val.1.continuous.intervalIntegrable _ _)
    (second.val.1.continuous.intervalIntegrable _ _)

theorem c1AngularIntegral_smul (scalar : ℂ) (data : PeriodicC1HolderHalf) :
    c1AngularIntegralCCLM (scalar • data) = scalar * c1AngularIntegralCCLM data := by
  change (∫ label in (0 : ℝ)..(2 * Real.pi), scalar * data.val.1 label) = _
  exact intervalIntegral.integral_const_mul scalar _

theorem c1AngularIntegral_hilbert (data : PeriodicC1HolderHalf) :
    c1AngularIntegralCCLM (periodicHilbertC1 data) = 0 := periodicHilbertC1_mean_zero data

theorem periodicHilbertPositiveProjection_mean_zero (data : PeriodicC1HolderHalf) :
    c1AngularIntegralCCLM (periodicHilbertPositiveProjection data) = 0 := by
  rw [periodicHilbertPositiveProjection_apply, c1AngularIntegral_smul,
    c1AngularIntegral_add, c1AngularIntegral_smul,
    periodicMeanZeroPartCCLM_integral, c1AngularIntegral_hilbert, mul_zero, add_zero, mul_zero]

theorem periodicHilbertNegativeProjection_mean_zero (data : PeriodicC1HolderHalf) :
    c1AngularIntegralCCLM (periodicHilbertNegativeProjection data) = 0 := by
  rw [periodicHilbertNegativeProjection_apply, c1AngularIntegral_smul,
    c1AngularIntegral_sub, c1AngularIntegral_smul,
    periodicMeanZeroPartCCLM_integral, c1AngularIntegral_hilbert, mul_zero, sub_zero, mul_zero]

theorem periodicHilbertPositiveProjection_idempotent (data : PeriodicC1HolderHalf) :
    periodicHilbertPositiveProjection (periodicHilbertPositiveProjection data) =
      periodicHilbertPositiveProjection data := by
  rw [periodicHilbertPositiveProjection_apply,
    periodicMeanZeroPartCCLM_of_integral_zero _ (periodicHilbertPositiveProjection_mean_zero data),
    periodicHilbertC1_positiveProjection]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (1 / 2 : ℂ) * ((periodicHilbertPositiveProjection data).val.1 label +
    Complex.I * ((-Complex.I) * (periodicHilbertPositiveProjection data).val.1 label)) = _
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem periodicHilbertNegativeProjection_idempotent (data : PeriodicC1HolderHalf) :
    periodicHilbertNegativeProjection (periodicHilbertNegativeProjection data) =
      periodicHilbertNegativeProjection data := by
  rw [periodicHilbertNegativeProjection_apply,
    periodicMeanZeroPartCCLM_of_integral_zero _ (periodicHilbertNegativeProjection_mean_zero data),
    periodicHilbertC1_negativeProjection]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (1 / 2 : ℂ) * ((periodicHilbertNegativeProjection data).val.1 label -
    Complex.I * (Complex.I * (periodicHilbertNegativeProjection data).val.1 label)) = _
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem periodicHilbertPositiveProjection_negative (data : PeriodicC1HolderHalf) :
    periodicHilbertPositiveProjection (periodicHilbertNegativeProjection data) = 0 := by
  rw [periodicHilbertPositiveProjection_apply,
    periodicMeanZeroPartCCLM_of_integral_zero _ (periodicHilbertNegativeProjection_mean_zero data),
    periodicHilbertC1_negativeProjection]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (1 / 2 : ℂ) * ((periodicHilbertNegativeProjection data).val.1 label +
    Complex.I * (Complex.I * (periodicHilbertNegativeProjection data).val.1 label)) = 0
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem periodicHilbertNegativeProjection_positive (data : PeriodicC1HolderHalf) :
    periodicHilbertNegativeProjection (periodicHilbertPositiveProjection data) = 0 := by
  rw [periodicHilbertNegativeProjection_apply,
    periodicMeanZeroPartCCLM_of_integral_zero _ (periodicHilbertPositiveProjection_mean_zero data),
    periodicHilbertC1_positiveProjection]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (1 / 2 : ℂ) * ((periodicHilbertPositiveProjection data).val.1 label -
    Complex.I * ((-Complex.I) * (periodicHilbertPositiveProjection data).val.1 label)) = 0
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem periodicHilbertPositiveProjection_norm_bound (data : PeriodicC1HolderHalf) :
    ‖periodicHilbertPositiveProjection data‖ ≤ (1 + periodicHilbertBound) * ‖data‖ := by
  rw [periodicHilbertPositiveProjection_apply]
  have halfNorm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  have imaginaryBound : ‖Complex.I • periodicHilbertC1 data‖ ≤ 2 * periodicHilbertBound * ‖data‖ := by
    calc
      _ ≤ ‖Complex.I‖ * ‖periodicHilbertC1 data‖ := norm_smul_le _ _
      _ ≤ _ := by simpa only [Complex.norm_I, one_mul] using periodicHilbertC1_norm_bound data
  calc
    _ ≤ ‖(1 / 2 : ℂ)‖ * ‖periodicMeanZeroPartCCLM data + Complex.I • periodicHilbertC1 data‖ := norm_smul_le _ _
    _ ≤ (1 / 2 : ℝ) * (2 * ‖data‖ + 2 * periodicHilbertBound * ‖data‖) := by
      rw [halfNorm]
      exact mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add (periodicMeanZeroPartCCLM_norm_bound data) imaginaryBound)) (by norm_num)
    _ = _ := by ring

theorem periodicHilbertNegativeProjection_norm_bound (data : PeriodicC1HolderHalf) :
    ‖periodicHilbertNegativeProjection data‖ ≤ (1 + periodicHilbertBound) * ‖data‖ := by
  rw [periodicHilbertNegativeProjection_apply]
  have halfNorm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  have imaginaryBound : ‖Complex.I • periodicHilbertC1 data‖ ≤ 2 * periodicHilbertBound * ‖data‖ := by
    calc
      _ ≤ ‖Complex.I‖ * ‖periodicHilbertC1 data‖ := norm_smul_le _ _
      _ ≤ _ := by simpa only [Complex.norm_I, one_mul] using periodicHilbertC1_norm_bound data
  calc
    _ ≤ ‖(1 / 2 : ℂ)‖ * ‖periodicMeanZeroPartCCLM data - Complex.I • periodicHilbertC1 data‖ := norm_smul_le _ _
    _ ≤ (1 / 2 : ℝ) * (2 * ‖data‖ + 2 * periodicHilbertBound * ‖data‖) := by
      rw [halfNorm]
      exact mul_le_mul_of_nonneg_left
        ((norm_sub_le _ _).trans (add_le_add (periodicMeanZeroPartCCLM_norm_bound data) imaginaryBound)) (by norm_num)
    _ = _ := by ring

end

end EulerNonuniqueness.Paper
