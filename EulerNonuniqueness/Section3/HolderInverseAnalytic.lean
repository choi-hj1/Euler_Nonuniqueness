import EulerNonuniqueness.Section3.HolderDifferentialAlgebra
import EulerNonuniqueness.Section3.C1HolderOperations
import Mathlib.Analysis.Analytic.Constructions

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance holderInverseAnalyticRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance holderInverseAnalyticOperatorGroup : NormedAddCommGroup (PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance holderInverseAnalyticOperatorSpace : NormedSpace ℝ (PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance holderInverseAnalyticOperatorRing : NormedRing (PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedRing (𝕜 := ℝ) (E := PeriodicHolderHalf)
local instance holderInverseAnalyticOperatorAlgebra : NormedAlgebra ℝ (PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAlgebra (𝕜 := ℝ) (E := PeriodicHolderHalf)
local instance holderInverseAnalyticUniformGroup : IsUniformAddGroup PeriodicHolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicHolderHalf)
local instance holderInverseAnalyticOperatorComplete : CompleteSpace (PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.instCompleteSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf)

def holderMultiplierUnit (data : PeriodicHolderHalf) {lower : ℝ} (positive : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) : (PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf)ˣ where
  val := holderProductRealCLM data
  inv := holderProductRealCLM (holderInverse data positive separated)
  val_inv := by
    apply ContinuousLinearMap.ext
    intro value
    apply PeriodicHolderHalf.ext_value
    intro label
    change data.val.1 label * ((data.val.1 label)⁻¹ * value.val.1 label) = value.val.1 label
    rw [← mul_assoc, mul_inv_cancel₀, one_mul]
    exact norm_ne_zero_iff.mp (ne_of_gt (positive.trans_le (separated label)))
  inv_val := by
    apply ContinuousLinearMap.ext
    intro value
    apply PeriodicHolderHalf.ext_value
    intro label
    change (data.val.1 label)⁻¹ * (data.val.1 label * value.val.1 label) = value.val.1 label
    rw [← mul_assoc, inv_mul_cancel₀, one_mul]
    exact norm_ne_zero_iff.mp (ne_of_gt (positive.trans_le (separated label)))

theorem holderInverse_eq_multiplier_inverse (data : PeriodicHolderHalf) {lower : ℝ}
    (positive : 0 < lower) (separated : ∀ label, lower ≤ ‖data.val.1 label‖) :
    extendedHolderInverse data =
      (Ring.inverse (holderProductRealCLM data)) (c1ValueHolder (c1Constant 1)) := by
  have inverse := Ring.inverse_unit (holderMultiplierUnit data positive separated)
  change Ring.inverse (holderProductRealCLM data) =
    holderProductRealCLM (holderInverse data positive separated) at inverse
  rw [inverse, extendedHolderInverse_eq data positive separated]
  apply PeriodicHolderHalf.ext_value
  intro label
  change (data.val.1 label)⁻¹ = (data.val.1 label)⁻¹ * 1
  exact (mul_one _).symm

theorem analyticAt_extendedHolderInverse (data : PeriodicHolderHalf) {lower : ℝ}
    (positive : 0 < lower) (separated : ∀ label, lower ≤ ‖data.val.1 label‖) :
    AnalyticAt ℝ extendedHolderInverse data := by
  have inverse : AnalyticAt ℝ Ring.inverse (holderProductRealCLM data) :=
    analyticAt_inverse (𝕜 := ℝ) (A := PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf)
      (holderMultiplierUnit data positive separated)
  have multiplier : AnalyticAt ℝ (fun current : PeriodicHolderHalf => Ring.inverse (holderProductRealCLM current)) data :=
    inverse.comp (holderProductRealCLM.analyticAt data)
  have candidate : AnalyticAt ℝ (fun current : PeriodicHolderHalf =>
      (Ring.inverse (holderProductRealCLM current)) (c1ValueHolder (c1Constant 1))) data :=
    ((ContinuousLinearMap.apply ℝ PeriodicHolderHalf (c1ValueHolder (c1Constant 1))).analyticAt _).comp multiplier
  apply candidate.congr
  filter_upwards [Metric.ball_mem_nhds data (half_pos positive)] with current member
  have perturbation : ‖current - data‖ ≤ lower / 2 := by
    exact (show ‖current - data‖ < lower / 2 from by simpa only [Metric.mem_ball, dist_eq_norm] using member).le
  have next_separated := holder_perturbation_separated data (current - data) separated perturbation
  rw [add_sub_cancel] at next_separated
  exact (holderInverse_eq_multiplier_inverse current (half_pos positive) next_separated).symm

end

end EulerNonuniqueness.Paper
