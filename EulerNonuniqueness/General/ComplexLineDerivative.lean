import Mathlib

namespace EulerNonuniqueness.General

open Filter
open scoped Topology

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℂ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℂ Target]

noncomputable def complexLineDerivative (function : Domain → Target) (point direction : Domain) : Target :=
  deriv (fun parameter : ℂ => function (point + parameter • direction)) 0

theorem complexLineDerivative_smul
    (function : Domain → Target) (point direction : Domain) (scalar : ℂ)
    (differentiable : DifferentiableAt ℂ
      (fun parameter : ℂ => function (point + parameter • direction)) 0) :
    complexLineDerivative function point (scalar • direction) =
      scalar • complexLineDerivative function point direction := by
  have outer : HasDerivAt (fun parameter : ℂ => function (point + parameter • direction))
      (complexLineDerivative function point direction) (scalar * 0) := by
    simpa only [mul_zero, complexLineDerivative] using differentiable.hasDerivAt
  have inner : HasDerivAt (fun parameter : ℂ => scalar * parameter) scalar 0 := by
    simpa only [mul_one] using (hasDerivAt_id (0 : ℂ)).const_mul scalar
  have composed := outer.scomp (0 : ℂ) inner
  change HasDerivAt (fun parameter : ℂ => function (point + (scalar * parameter) • direction))
    (scalar • complexLineDerivative function point direction) 0 at composed
  have curve : (fun parameter : ℂ => function (point + (scalar * parameter) • direction)) =
      (fun parameter : ℂ => function (point + parameter • (scalar • direction))) := by
    funext parameter
    rw [smul_smul, mul_comm parameter scalar]
  rw [curve] at composed
  exact composed.deriv

theorem differentiableAt_complex_line_of_analyticAt_shift
    (function : Domain → Target) (point direction : Domain) (parameter : ℂ)
    (holomorphic : AnalyticAt ℂ (fun current : ℂ =>
      function (point + parameter • direction + current • direction)) 0) :
    DifferentiableAt ℂ (fun current : ℂ => function (point + current • direction)) parameter := by
  have outer : DifferentiableAt ℂ (fun current : ℂ =>
      function (point + parameter • direction + current • direction)) (parameter - parameter) := by
    simpa only [sub_self] using holomorphic.differentiableAt
  have inner : DifferentiableAt ℂ (fun current : ℂ => current - parameter) parameter :=
    differentiableAt_id.sub (differentiableAt_const parameter)
  have translated := outer.comp (f := fun current : ℂ => current - parameter) parameter inner
  apply translated.congr_of_eventuallyEq
  filter_upwards [] with current
  dsimp only [Function.comp_apply]
  apply congrArg function
  module

theorem complexLineDerivative_smul_total
    (function : Domain → Target) (point direction : Domain) (scalar : ℂ) :
    complexLineDerivative function point (scalar • direction) =
      scalar • complexLineDerivative function point direction := by
  by_cases scalarZero : scalar = 0
  · subst scalar
    simp only [complexLineDerivative, zero_smul, smul_zero, add_zero, deriv_const]
  by_cases differentiable : DifferentiableAt ℂ
      (fun parameter : ℂ => function (point + parameter • direction)) 0
  · exact complexLineDerivative_smul function point direction scalar differentiable
  have scaledNotDifferentiable : ¬DifferentiableAt ℂ
      (fun parameter : ℂ => function (point + parameter • (scalar • direction))) 0 := by
    intro scaledDifferentiable
    apply differentiable
    have inner : DifferentiableAt ℂ (fun parameter : ℂ => scalar⁻¹ * parameter) 0 :=
      differentiableAt_const scalar⁻¹ |>.mul differentiableAt_id
    have outer : DifferentiableAt ℂ
        (fun parameter : ℂ => function (point + parameter • (scalar • direction))) (scalar⁻¹ * 0) := by
      simpa only [mul_zero] using scaledDifferentiable
    have composed := outer.comp (0 : ℂ) inner
    apply composed.congr_of_eventuallyEq
    filter_upwards [] with parameter
    dsimp only [Function.comp_apply]
    apply congrArg function
    apply congrArg (fun vector : Domain => point + vector)
    rw [smul_smul]
    congr 1
    field_simp
  rw [complexLineDerivative, deriv_zero_of_not_differentiableAt scaledNotDifferentiable,
    complexLineDerivative, deriv_zero_of_not_differentiableAt differentiable, smul_zero]

end EulerNonuniqueness.General
