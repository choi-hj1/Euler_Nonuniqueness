import EulerNonuniqueness.Section3.DiskChartedEulerField
import EulerNonuniqueness.Section3.DiskForcingModes

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance velocityTranslationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem extendedContourVelocity_translate (data : PeriodicC1HolderHalf) (translation : ℂ)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (translatedSmall : ‖data + c1Constant translation - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    extendedContourVelocity (data + c1Constant translation) = extendedContourVelocity data := by
  rw [extendedContourVelocity_eq _ translatedSmall, extendedContourVelocity_eq _ small]
  apply PeriodicC1HolderHalf.ext_value
  intro target
  rw [contourVelocityBanach_value, contourVelocityBanach_value]
  unfold contourVelocity
  congr 1
  apply intervalIntegral.integral_congr
  intro source _inside
  change Real.log ‖(data.val.1 target + translation) - (data.val.1 source + translation)‖ •
      (data.val.2.val.1 source + 0) = _
  rw [add_sub_add_right_eq_sub, add_zero]

theorem fderiv_extendedContourVelocity_circle_constant (constant : ℂ) :
    fderiv ℝ extendedContourVelocity standardCircleBanach (c1Constant constant) = 0 := by
  have positive : (0 : ℝ) < min 1 (2 / (3 * Real.pi)) := by positivity
  have small : ‖standardCircleBanach - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by simpa using positive
  have lineJet : HasDerivAt (fun scalar : ℝ => standardCircleBanach + scalar • c1Constant constant)
      (c1Constant constant) 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (c1Constant constant)).const_add standardCircleBanach
  have selfJet := (differentiableAt_extendedContourVelocity standardCircleBanach small).hasFDerivAt
  have selfAtLine : HasFDerivAt extendedContourVelocity (fderiv ℝ extendedContourVelocity standardCircleBanach)
      (standardCircleBanach + (0 : ℝ) • c1Constant constant) := by simpa only [zero_smul, add_zero] using selfJet
  have actual := selfAtLine.comp_hasDerivAt 0 lineJet
  have normLimit : Tendsto (fun scalar : ℝ => ‖standardCircleBanach + scalar • c1Constant constant - standardCircleBanach‖)
      (𝓝 0) (𝓝 0) := by
    have continuous : Continuous (fun scalar : ℝ => ‖standardCircleBanach + scalar • c1Constant constant - standardCircleBanach‖) := by fun_prop
    simpa only [zero_smul, add_zero, sub_self, norm_zero] using continuous.tendsto (0 : ℝ)
  have near := normLimit.eventually (gt_mem_nhds positive)
  have identity : (fun scalar : ℝ => extendedContourVelocity (standardCircleBanach + scalar • c1Constant constant)) =ᶠ[𝓝 0]
      fun _ => extendedContourVelocity standardCircleBanach := by
    filter_upwards [near] with scalar nearby
    have constantIdentity : scalar • c1Constant constant = c1Constant (scalar • constant) := by
      exact (c1ConstantCLM.map_smul scalar constant).symm
    rw [constantIdentity] at nearby ⊢
    exact extendedContourVelocity_translate standardCircleBanach (scalar • constant) small nearby
  exact actual.unique ((hasDerivAt_const (0 : ℝ) (extendedContourVelocity standardCircleBanach)).congr_of_eventuallyEq identity)

theorem diskRotatingDerivative_constant (constant : ℂ) :
    diskRotatingDerivative (c1Constant constant) = c1Constant ((-Complex.I / 2) * constant) := by
  rw [diskRotatingDerivative_apply, fderiv_extendedContourVelocity_circle_constant, zero_sub]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change -((Complex.I / 2) * constant) = (-Complex.I / 2) * constant
  ring

end EulerNonuniqueness.Paper
