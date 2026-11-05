import EulerNonuniqueness.Section3.RotatingForcingRelabelResidual
import EulerNonuniqueness.Section3.ContourVelocityQuadraticDerivative

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance rotatingSecondJetC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule

theorem diskEulerRotatingField_second_derivative (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    fderiv ℝ (fderiv ℝ diskEulerRotatingField) data =
      fderiv ℝ (fderiv ℝ extendedContourVelocity) data := by
  have neighborhood : ∀ᶠ current in 𝓝 data,
      ‖current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) :=
    (isOpen_lt ((continuous_id.sub continuous_const).norm) continuous_const).mem_nhds small
  have identity : (fun current => fderiv ℝ diskEulerRotatingField current) =ᶠ[𝓝 data]
      (fun current => fderiv ℝ extendedContourVelocity current - c1ProductCLM (c1Constant (Complex.I / 2))) := by
    filter_upwards [neighborhood] with current currentSmall
    have rotation : HasFDerivAt (c1Product (c1Constant (Complex.I / 2)))
        (c1ProductCLM (c1Constant (Complex.I / 2))) current :=
      ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
        (F := PeriodicC1HolderHalf) (c1ProductCLM (c1Constant (Complex.I / 2)))
    exact ((differentiableAt_extendedContourVelocity current currentSmall).hasFDerivAt.sub
      rotation).fderiv
  exact identity.fderiv_eq.trans (fderiv_sub_const _)

theorem diskEulerRotatingField_second_derivative_apply (data first second : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    fderiv ℝ (fderiv ℝ diskEulerRotatingField) data first second =
      (2 : ℝ) • contourVelocityQuadraticDerivativeCLM data first second := by
  rw [diskEulerRotatingField_second_derivative data small]
  unfold contourVelocityQuadraticDerivativeCLM
  change fderiv ℝ (fderiv ℝ extendedContourVelocity) data first second =
    (2 : ℝ) • ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ extendedContourVelocity) data first second)
  rw [smul_smul]
  norm_num

end EulerNonuniqueness.Paper
