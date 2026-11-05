import EulerNonuniqueness.Section3.HolderContinuousVectors
import EulerNonuniqueness.Section3.ContourSteklovSmoothing

noncomputable section

open scoped BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] continuousFourierC1Group holderContinuousRealSpace
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem contourPureLabelAction_tangent (time : ℝ) (data : PeriodicC1HolderHalf) :
    (contourPureLabelAction time data).val.2 = holderPureLabelAction time data.val.2 := by
  apply PeriodicHolderHalf.ext_value
  intro label
  change standardCircle time * ((standardCircle time)⁻¹ * data.val.2.val.1 (label + time)) =
    data.val.2.val.1 (label + time)
  rw [← mul_assoc, mul_inv_cancel₀ (by simp [standardCircle, Complex.exp_ne_zero]), one_mul]

def contourTangentHolderCLM : PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf :=
  (ContinuousLinearMap.snd ℝ (ℝ →ᵇ ℂ) PeriodicHolderHalf).comp periodicC1HolderGraph.subtypeL

theorem contourContinuousVector_tangent (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) : data.val.2 ∈ holderContinuousVectorSubmodule := by
  have continuous := contourTangentHolderCLM.continuous.comp (continuous_contourLabelShiftCCLM data member)
  change Continuous (fun time => contourTangentHolderCLM (contourLabelShiftCCLM time data)) at continuous
  have identity : (fun time => contourTangentHolderCLM (contourLabelShiftCCLM time data)) =
      fun time => holderPureLabelAction time data.val.2 := by
    funext time
    exact contourPureLabelAction_tangent time data
  rw [identity] at continuous
  exact continuous

theorem continuous_contourPureLabelAction_values (data : PeriodicC1HolderHalf) :
    Continuous (fun time => (contourPureLabelAction time data).val.1) := by
  have bound : LipschitzWith ⟨‖data‖, norm_nonneg data⟩ (fun time => (contourPureLabelAction time data).val.1) := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    rw [dist_eq_norm, Real.dist_eq]
    apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg data) (abs_nonneg _))).mpr
    intro label
    change ‖(contourLabelShiftCCLM first data).val.1 label - (contourLabelShiftCCLM second data).val.1 label‖ ≤ _
    rw [contourLabelShiftCCLM_value, contourLabelShiftCCLM_value]
    simpa only [NNReal.coe_mk, add_sub_add_left_eq_sub] using
      PeriodicC1HolderHalf.lipschitz_bound data (label + first) (label + second)
  exact bound.continuous

theorem contourContinuousVector_of_tangent (data : PeriodicC1HolderHalf)
    (member : data.val.2 ∈ holderContinuousVectorSubmodule) : data ∈ contourContinuousVectorSubmodule := by
  have valueContinuous := continuous_contourPureLabelAction_values data
  have tangentContinuous : Continuous (fun time => (contourPureLabelAction time data).val.2) := by
    have identity : (fun time => (contourPureLabelAction time data).val.2) =
        fun time => holderPureLabelAction time data.val.2 := funext fun time => contourPureLabelAction_tangent time data
    rw [identity]
    exact member
  have pure : Continuous (fun time => contourPureLabelAction time data) := by
    exact (valueContinuous.prodMk tangentContinuous).subtype_mk (fun time => (contourPureLabelAction time data).property)
  have circleContinuous : Continuous standardCircle := by unfold standardCircle; fun_prop
  have continuous := circleContinuous.star.smul pure
  have identity : (fun time => star (standardCircle time) • contourPureLabelAction time data) =
      fun time => normalizedContourShiftCLM time data := by
    funext time
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change star (standardCircle time) * (contourLabelShiftCCLM time data).val.1 label =
      (normalizedContourShift time data).val.1 label
    rw [contourLabelShiftCCLM_value, normalizedContourShift_value, standardCircle_star_eq_inv]
  rw [identity] at continuous
  exact continuous

theorem contourContinuousVector_iff_tangent (data : PeriodicC1HolderHalf) :
    data ∈ contourContinuousVectorSubmodule ↔ data.val.2 ∈ holderContinuousVectorSubmodule :=
  ⟨contourContinuousVector_tangent data, contourContinuousVector_of_tangent data⟩

end EulerNonuniqueness.Paper
