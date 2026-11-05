import EulerNonuniqueness.Section3.FiniteLiteralPatchMoments
import EulerNonuniqueness.Section3.PolarArea

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem affinePatchDomain_congr (center : ℂ) (radius : ℝ)
    {first second : PeriodicC1HolderHalf} (equal : first = second)
    (first_small : ‖first - standardCircleBanach‖ < 1 / 3)
    (second_small : ‖second - standardCircleBanach‖ < 1 / 3) :
    affinePatchDomain center radius first first_small = affinePatchDomain center radius second second_small := by
  cases equal
  rfl

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem domain_area_hasDerivAt (flow : FiniteLiteralPatchFlow configuration) {time : ℝ}
    (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    HasDerivAt (fun parameter => (volume (flow.domain parameter index)).toReal) 0 time := by
  have derivative := flow.domain_integral_hasDerivAt inside index (fun _ => (1 : ℝ))
    (fun _ => (0 : ℂ →L[ℝ] ℝ)) continuous_const continuous_const
    (fun position => hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) position)
  simpa only [ContinuousLinearMap.zero_apply, integral_zero, setIntegral_const, smul_eq_mul, mul_one] using derivative

theorem domain_area_eq_initial (flow : FiniteLiteralPatchFlow configuration) {time : ℝ}
    (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    (volume (flow.domain time index)).toReal = (volume (flow.domain 0 index)).toReal := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun parameter member => (flow.domain_area_hasDerivAt member index).differentiableAt.differentiableWithinAt)
    (fun parameter member => (flow.domain_area_hasDerivAt member index).deriv) inside
  exact ⟨by linarith [flow.duration_positive], flow.duration_positive⟩

theorem domain_initial_area (flow : FiniteLiteralPatchFlow configuration) (index : Fin count) :
    (volume (flow.domain 0 index)).toReal = Real.pi * configuration.radius index ^ 2 := by
  have initial_component : flow.shape 0 index = standardCircleBanach := congrFun flow.initial index
  have small : ‖standardCircleBanach - standardCircleBanach‖ < 1 / 3 := by norm_num
  have domain_identity : flow.domain 0 index =
      affinePatchDomain (configuration.center index) (configuration.radius index) standardCircleBanach small := by
    dsimp only [domain, FiniteContourConfiguration.literalDomain]
    exact affinePatchDomain_congr _ _ initial_component _ small
  have unit_area : (volume (nearCircleInterior standardCircleBanach small)).toReal = Real.pi := by
    rw [nearCircleInterior_area]
    simp_rw [nearCircleRadialProfile_standardCircle]
    simp only [one_pow, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  rw [domain_identity, affinePatchDomain_area _ (configuration.radius_pos index), unit_area]
  ring

theorem domain_area (flow : FiniteLiteralPatchFlow configuration) {time : ℝ}
    (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    (volume (flow.domain time index)).toReal = Real.pi * configuration.radius index ^ 2 := by
  rw [flow.domain_area_eq_initial inside index, flow.domain_initial_area index]

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
