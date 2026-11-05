import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem fderiv_linear_equivariant (function : Space → Space) (linear : Space →L[ℝ] Space) (base : Space)
    (baseRegular : DifferentiableAt ℝ function base) (imageRegular : DifferentiableAt ℝ function (linear base))
    (equivariant : (fun point => function (linear point)) =ᶠ[𝓝 base] (fun point => linear (function point))) :
    (fderiv ℝ function (linear base)).comp linear = linear.comp (fderiv ℝ function base) := by
  have first := imageRegular.hasFDerivAt.comp base linear.hasFDerivAt
  have second := linear.hasFDerivAt.comp base baseRegular.hasFDerivAt
  exact first.unique (second.congr_of_eventuallyEq equivariant)

theorem second_linear_equivariant (operator : Space → Space →L[ℝ] Space)
    (linear : Space →L[ℝ] Space) (base : Space)
    (baseRegular : DifferentiableAt ℝ operator base) (imageRegular : DifferentiableAt ℝ operator (linear base))
    (equivariant : ∀ᶠ point in 𝓝 base, ∀ direction : Space,
      operator (linear point) (linear direction) = linear (operator point direction))
    (firstDirection secondDirection : Space) :
    fderiv ℝ operator (linear base) (linear firstDirection) (linear secondDirection) =
      linear (fderiv ℝ operator base firstDirection secondDirection) := by
  let firstEvaluation : (Space →L[ℝ] Space) →L[ℝ] Space := ContinuousLinearMap.apply ℝ Space (linear secondDirection)
  let secondEvaluation : (Space →L[ℝ] Space) →L[ℝ] Space := ContinuousLinearMap.apply ℝ Space secondDirection
  have first := firstEvaluation.hasFDerivAt.comp base
    (imageRegular.hasFDerivAt.comp base linear.hasFDerivAt)
  have second := linear.hasFDerivAt.comp base (secondEvaluation.hasFDerivAt.comp base baseRegular.hasFDerivAt)
  have equality : (fun point => firstEvaluation (operator (linear point))) =ᶠ[𝓝 base]
      (fun point => linear (secondEvaluation (operator point))) := equivariant.mono fun _ identity => identity secondDirection
  have identity := first.unique (second.congr_of_eventuallyEq equality)
  exact congrArg (fun derivative : Space →L[ℝ] Space => derivative firstDirection) identity

end EulerNonuniqueness.General
