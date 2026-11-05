import EulerNonuniqueness.Section3.NormalizedShiftDerivative
import EulerNonuniqueness.General.ContinuousVectorSubmodule
import EulerNonuniqueness.General.ContinuousVectorBilinear

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule

def contourContinuousVectorSubmodule : Submodule ℝ PeriodicC1HolderHalf := by
  with_reducible
    exact EulerNonuniqueness.General.continuousVectorSubmodule (Space := PeriodicC1HolderHalf) normalizedContourShiftCLM

theorem contourContinuousVectorSubmodule_closed : IsClosed (contourContinuousVectorSubmodule : Set PeriodicC1HolderHalf) := by
  unfold contourContinuousVectorSubmodule
  with_reducible
    exact EulerNonuniqueness.General.continuousVectorSubmodule_closed normalizedContourShiftCLM
      (fun offset data => (normalizedContourShift_norm offset data).le)

theorem standardCircle_mem_contourContinuousVectorSubmodule : standardCircleBanach ∈ contourContinuousVectorSubmodule := by
  change Continuous (fun offset => normalizedContourShiftCLM offset standardCircleBanach)
  simpa only [normalizedContourShiftCLM_apply, normalizedContourShift_circle] using
    (continuous_const : Continuous (fun _ : ℝ => standardCircleBanach))

theorem contourContinuousVectorSubmodule_velocity (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    extendedContourVelocity data ∈ contourContinuousVectorSubmodule := by
  have orbit : Continuous (fun offset => normalizedContourShiftCLM offset data) := member
  have composition : Continuous (fun offset => extendedContourVelocity (normalizedContourShiftCLM offset data)) := by
    apply continuous_iff_continuousAt.mpr
    intro offset
    have shiftedSmall : ‖normalizedContourShift offset data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
      rw [normalizedContourShift_distance_circle]
      exact small
    have outer : ContinuousAt extendedContourVelocity (normalizedContourShiftCLM offset data) := by
      rw [normalizedContourShiftCLM_apply]
      with_reducible
        exact DifferentiableAt.continuousAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
          (differentiableAt_extendedContourVelocity _ shiftedSmall)
    exact ContinuousAt.comp (f := fun parameter : ℝ => normalizedContourShiftCLM parameter data)
      (g := extendedContourVelocity) (x := offset) outer (orbit.continuousAt (x := offset))
  change Continuous (fun offset => normalizedContourShiftCLM offset (extendedContourVelocity data))
  convert composition using 1
  funext offset
  exact (extendedContourVelocity_normalized_shift data offset small).symm

theorem contourContinuousVectorSubmodule_quadratic (first second : PeriodicC1HolderHalf)
    (firstMember : first ∈ contourContinuousVectorSubmodule)
    (secondMember : second ∈ contourContinuousVectorSubmodule) :
    contourVelocityQuadraticDerivativeCLM standardCircleBanach first second ∈ contourContinuousVectorSubmodule := by
  unfold contourContinuousVectorSubmodule at firstMember secondMember ⊢
  with_reducible
    exact EulerNonuniqueness.General.continuousVectorSubmodule_bilinear normalizedContourShiftCLM
      (contourVelocityQuadraticDerivativeCLM standardCircleBanach)
      (fun offset firstDirection secondDirection => by
        simpa only [normalizedContourShiftCLM_apply] using
          (contourVelocity_quadratic_normalized_shift offset firstDirection secondDirection).symm)
      first second firstMember secondMember

end

end EulerNonuniqueness.Paper
