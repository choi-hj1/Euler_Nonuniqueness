import EulerNonuniqueness.General.LocalThirdUniformBall
import EulerNonuniqueness.General.SecondDerivativeSymmetryBall
import EulerNonuniqueness.General.HalfSymmetricBilinear

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] relativeCubicBilinearGroup relativeCubicBilinearSpace
  relativeCubicThirdGroup relativeCubicThirdSpace

theorem exists_parameter_lipschitz_cubic_taylor_ball
    (function : Space → Space) (quadratic : Space → BilinearEnd Space)
    (first : ∀ᶠ point in 𝓝 (0 : Space), DifferentiableAt ℝ function point)
    (regular : HasLipschitzSecondDerivativeNear (fderiv ℝ function) (0 : Space))
    (quadraticApply : ∀ base left right,
      quadratic base left right = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ function) base left right) :
    ∃ radius > 0, ∃ constant : NNReal, ∀ initial final increment : Space,
      ‖initial‖ + ‖increment‖ ≤ radius → ‖final‖ + ‖increment‖ ≤ radius →
      ‖(function (initial + increment) - function initial - fderiv ℝ function initial increment -
          quadratic initial increment increment) -
        (function (final + increment) - function final - fderiv ℝ function final increment -
          quadratic final increment increment)‖ ≤
        (constant : ℝ) * ‖initial - final‖ * ‖increment‖ ^ 3 := by
  obtain ⟨outerRadius, positive, constant, derivatives, lipschitz⟩ :=
    exists_third_lipschitz_closedBall function 0 first regular
  let firstField := fderiv ℝ function
  let secondField := fderiv ℝ (fderiv ℝ function)
  let thirdField := fderiv ℝ (fderiv ℝ (fderiv ℝ function))
  have firstActual (point : Space) (inside : point ∈ closedBall 0 outerRadius) :
      HasFDerivAt function (firstField point) point := (derivatives point inside).1.hasFDerivAt
  have secondActual (point : Space) (inside : point ∈ closedBall 0 outerRadius) :
      HasFDerivAt firstField (secondField point) point := (derivatives point inside).2.1.hasFDerivAt
  have thirdActual (point : Space) (inside : point ∈ closedBall 0 outerRadius) :
      HasFDerivAt secondField (thirdField point) point := (derivatives point inside).2.2.hasFDerivAt
  have secondIdentity (point : Space) (inside : point ∈ ball 0 outerRadius) :
      secondField point = quadratic point + (quadratic point).flip := by
    apply ContinuousLinearMap.ext
    intro left
    apply ContinuousLinearMap.ext
    intro right
    have symmetric := second_derivative_symmetric_on_ball function firstField secondField
      0 firstActual secondActual point inside left right
    have halfIdentity := eq_half_add_half_of_eq symmetric
    change secondField point left right = quadratic point left right + quadratic point right left
    exact halfIdentity.trans (congrArg₂ (fun initial final : Space => initial + final)
      (quadraticApply point left right).symm (quadraticApply point right left).symm)
  refine ⟨outerRadius / 2, by positivity, constant, ?_⟩
  intro initial final increment initialInside finalInside
  have initialBase : initial ∈ ball 0 outerRadius := by
    apply mem_ball_zero_iff.mpr
    have nonnegative := norm_nonneg increment
    linarith
  have finalBase : final ∈ ball 0 outerRadius := by
    apply mem_ball_zero_iff.mpr
    have nonnegative := norm_nonneg increment
    linarith
  have initialOuter : ‖initial‖ + ‖increment‖ ≤ outerRadius := by linarith
  have finalOuter : ‖final‖ + ‖increment‖ ≤ outerRadius := by linarith
  exact norm_cubic_taylor_remainder_difference_of_lipschitz_third function firstField secondField thirdField
    constant firstActual secondActual thirdActual lipschitz initial final increment initialOuter finalOuter
    (quadratic initial) (quadratic final) (secondIdentity initial initialBase) (secondIdentity final finalBase)

end

end EulerNonuniqueness.General
