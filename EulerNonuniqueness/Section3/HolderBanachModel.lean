import EulerNonuniqueness.Section3.HolderBanach

open Set
open scoped BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

noncomputable section

theorem PeriodicHolderHalf.ext_value {first second : PeriodicHolderHalf}
    (equal : ∀ label : ℝ, first.val.1 label = second.val.1 label) : first = second := by
  apply Subtype.ext
  apply Prod.ext
  · exact BoundedContinuousFunction.ext equal
  · apply BoundedContinuousFunction.ext
    intro pair
    have root_ne : (Real.sqrt |pair.val.1 - pair.val.2| : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr pair.property))).ne'
    apply mul_left_cancel₀ root_ne
    rw [first.property.1 pair, second.property.1 pair, equal, equal]

def PeriodicC1HolderHalf.ofFunctions (function tangent : ℝ → ℂ)
    (function_continuous : Continuous function) (tangent_continuous : Continuous tangent)
    (valueBound speedBound holder : ℝ)
    (value_bound : ∀ label, ‖function label‖ ≤ valueBound)
    (speed_bound : ∀ label, ‖tangent label‖ ≤ speedBound)
    (holder_bound : ∀ first second : ℝ,
      ‖tangent first - tangent second‖ ≤ holder * Real.sqrt |first - second|)
    (derivative : ∀ label : ℝ, HasDerivAt function (tangent label) label)
    (periodic : Function.Periodic function (2 * Real.pi))
    (tangent_periodic : Function.Periodic tangent (2 * Real.pi)) : PeriodicC1HolderHalf :=
  ⟨(BoundedContinuousFunction.ofNormedAddCommGroup function function_continuous valueBound value_bound,
    PeriodicHolderHalf.ofFunction tangent tangent_continuous speedBound holder
      speed_bound holder_bound tangent_periodic), by
    constructor
    · intro label
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun current _ => derivative current)
        (tangent_continuous.intervalIntegrable 0 label)).symm
    · exact periodic⟩

theorem PeriodicC1HolderHalf.ofFunctions_norm_bound (function tangent : ℝ → ℂ)
    (function_continuous : Continuous function) (tangent_continuous : Continuous tangent)
    {valueBound speedBound holder : ℝ} (value_nonneg : 0 ≤ valueBound)
    (speed_nonneg : 0 ≤ speedBound) (holder_nonneg : 0 ≤ holder)
    (value_bound : ∀ label, ‖function label‖ ≤ valueBound)
    (speed_bound : ∀ label, ‖tangent label‖ ≤ speedBound)
    (holder_bound : ∀ first second : ℝ,
      ‖tangent first - tangent second‖ ≤ holder * Real.sqrt |first - second|)
    (derivative : ∀ label : ℝ, HasDerivAt function (tangent label) label)
    (periodic : Function.Periodic function (2 * Real.pi))
    (tangent_periodic : Function.Periodic tangent (2 * Real.pi)) :
    ‖PeriodicC1HolderHalf.ofFunctions function tangent function_continuous tangent_continuous
      valueBound speedBound holder value_bound speed_bound holder_bound derivative periodic tangent_periodic‖ ≤
      max valueBound (max speedBound holder) := by
  exact max_le_max
    (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le function_continuous value_nonneg value_bound)
    (PeriodicHolderHalf.ofFunction_norm_bound tangent tangent_continuous speed_nonneg holder_nonneg
      speed_bound holder_bound tangent_periodic)

theorem PeriodicC1HolderHalf.ext_value {first second : PeriodicC1HolderHalf}
    (equal : ∀ label : ℝ, first.val.1 label = second.val.1 label) : first = second := by
  apply Subtype.ext
  apply Prod.ext
  · exact BoundedContinuousFunction.ext equal
  · apply PeriodicHolderHalf.ext_value
    intro label
    have first_derivative := PeriodicC1HolderHalf.hasDerivAt first label
    have second_derivative := PeriodicC1HolderHalf.hasDerivAt second label
    have function_equal : (first.val.1 : ℝ → ℂ) = second.val.1 := funext equal
    rw [function_equal] at first_derivative
    exact first_derivative.unique second_derivative

theorem PeriodicC1HolderHalf.value_bound (data : PeriodicC1HolderHalf) (label : ℝ) :
    ‖data.val.1 label‖ ≤ ‖data‖ :=
  (data.val.1.norm_coe_le_norm label).trans (le_max_left _ _)

theorem PeriodicC1HolderHalf.speed_bound (data : PeriodicC1HolderHalf) (label : ℝ) :
    ‖data.val.2.val.1 label‖ ≤ ‖data‖ :=
  (PeriodicHolderHalf.value_bound data.val.2 label).trans (le_max_right _ _)

theorem PeriodicC1HolderHalf.periodic (data : PeriodicC1HolderHalf) :
    Function.Periodic data.val.1 (2 * Real.pi) := data.property.2

end

end EulerNonuniqueness.Paper
