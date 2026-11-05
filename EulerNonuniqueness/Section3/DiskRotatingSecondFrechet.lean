import EulerNonuniqueness.Section3.DiskRotatingSecondJet

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance rotatingSecondFrechetC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule

theorem diskEulerRotatingField_hasFDerivAt_fderiv (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    HasFDerivAt (fderiv ℝ diskEulerRotatingField)
      (fderiv ℝ (fderiv ℝ diskEulerRotatingField) data) data := by
  have rawJet := (differentiableAt_fderiv_extendedContourVelocity data small).hasFDerivAt
  have subtracted := rawJet.sub_const (c1ProductCLM (c1Constant (Complex.I / 2)))
  have neighborhood : ∀ᶠ current in 𝓝 data,
      ‖current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) :=
    (isOpen_lt ((continuous_id.sub continuous_const).norm) continuous_const).mem_nhds small
  have identity : (fderiv ℝ diskEulerRotatingField) =ᶠ[𝓝 data]
      (fun current => fderiv ℝ extendedContourVelocity current - c1ProductCLM (c1Constant (Complex.I / 2))) := by
    filter_upwards [neighborhood] with current currentSmall
    have rotation : HasFDerivAt (c1Product (c1Constant (Complex.I / 2)))
        (c1ProductCLM (c1Constant (Complex.I / 2))) current :=
      ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
        (F := PeriodicC1HolderHalf) (c1ProductCLM (c1Constant (Complex.I / 2)))
    exact ((differentiableAt_extendedContourVelocity current currentSmall).hasFDerivAt.sub rotation).fderiv
  rw [diskEulerRotatingField_second_derivative data small]
  exact subtracted.congr_of_eventuallyEq identity

end EulerNonuniqueness.Paper
