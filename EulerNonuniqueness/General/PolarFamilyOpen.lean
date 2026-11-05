import EulerNonuniqueness.General.PeriodicFamilyAngle

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness

theorem isOpen_periodic_polar_family {parameter : Type*} [TopologicalSpace parameter]
    (profile : parameter → ℝ → ℝ) (profileContinuous : Continuous (Function.uncurry profile))
    (periodic : ∀ point, Function.Periodic (profile point) (2 * Real.pi))
    {lower : ℝ} (lowerPositive : 0 < lower) (profileLower : ∀ point angle, lower ≤ profile point angle) :
    IsOpen {point : parameter × ℂ | ‖point.2‖ < profile point.1 (Complex.arg point.2)} := by
  rw [isOpen_iff_mem_nhds]
  intro point member
  by_cases zero : point.2 = 0
  · have eventual : ∀ᶠ next : parameter × ℂ in 𝓝 point, ‖next.2‖ < lower :=
      continuous_snd.norm.continuousAt.eventually_lt_const (by simpa only [zero, norm_zero] using lowerPositive)
    exact eventual.mono fun next bound => bound.trans_le (profileLower _ _)
  · exact continuous_snd.norm.continuousAt.eventually_lt
      (periodic_family_arg_continuousAt profile profileContinuous periodic zero) member

end EulerNonuniqueness
