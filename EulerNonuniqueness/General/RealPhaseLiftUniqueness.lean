import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.SeparatedMap

noncomputable section

open Set Function

namespace EulerNonuniqueness.General

theorem real_phase_lift_eqOn_Icc {path : ℝ → ℂ} {first second : ℝ → ℝ} {horizon : ℝ}
    (horizonNonnegative : 0 ≤ horizon)
    (firstContinuous : ContinuousOn first (Icc 0 horizon))
    (secondContinuous : ContinuousOn second (Icc 0 horizon))
    (nonzero : ∀ time ∈ Icc 0 horizon, path time ≠ 0)
    (firstPolar : ∀ time ∈ Icc 0 horizon, path time = (‖path time‖ : ℂ) * Complex.exp (Complex.I * (first time : ℂ)))
    (secondPolar : ∀ time ∈ Icc 0 horizon, path time = (‖path time‖ : ℂ) * Complex.exp (Complex.I * (second time : ℂ)))
    (initial : first 0 = second 0) : EqOn first second (Icc 0 horizon) := by
  apply (T2Space.isSeparatedMap Circle.exp).eqOn_of_comp_eqOn isLocalHomeomorph_circleExp.isLocallyInjective
    isPreconnected_Icc firstContinuous secondContinuous ?_ ⟨le_rfl, horizonNonnegative⟩ initial
  intro time member
  apply Subtype.ext
  have scalarNonzero : (‖path time‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (nonzero time member))
  have actual := mul_left_cancel₀ scalarNonzero ((firstPolar time member).symm.trans (secondPolar time member))
  simpa only [comp_apply, Circle.coe_exp, mul_comm] using actual

end EulerNonuniqueness.General
