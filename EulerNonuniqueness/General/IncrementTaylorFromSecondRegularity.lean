import EulerNonuniqueness.General.CubicTaylorIncrementDifference
import EulerNonuniqueness.General.HalfSymmetricBilinear
import EulerNonuniqueness.General.SecondDerivativeSymmetryBall
import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] relativeCubicBilinearGroup relativeCubicBilinearSpace

theorem exists_increment_quadratic_taylor_ball
    (function : Space → Space) (quadratic : Space → BilinearEnd Space)
    (first : ∀ᶠ point in 𝓝 (0 : Space), DifferentiableAt ℝ function point)
    (regular : HasLipschitzDerivativeNear (fderiv ℝ function) (0 : Space))
    (quadraticApply : ∀ base left right,
      quadratic base left right = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ function) base left right) :
    ∃ radius > 0, ∃ constant : NNReal, ∀ base initial final : Space,
      ‖base‖ + (‖initial‖ + ‖final‖) ≤ radius →
      ‖(function (base + initial) - function base - fderiv ℝ function base initial - quadratic base initial initial) -
        (function (base + final) - function base - fderiv ℝ function base final - quadratic base final final)‖ ≤
        (constant : ℝ) * (‖initial‖ + ‖final‖) ^ 2 * ‖initial - final‖ := by
  obtain ⟨constant, neighborhood, nearby, lipschitz⟩ := regular.2
  have combined : neighborhood ∩ {point | DifferentiableAt ℝ function point ∧
      DifferentiableAt ℝ (fderiv ℝ function) point} ∈ 𝓝 (0 : Space) := inter_mem nearby (first.and regular.1)
  obtain ⟨outerRadius, positive, contained⟩ := Metric.mem_nhds_iff.mp combined
  let firstField := fderiv ℝ function
  let secondField := fderiv ℝ (fderiv ℝ function)
  have firstActual (point : Space) (inside : point ∈ closedBall 0 (outerRadius / 2)) :
      HasFDerivAt function (firstField point) point := by
    have small : point ∈ ball 0 outerRadius := by
      apply mem_ball_zero_iff.mpr
      have bound := mem_closedBall_zero_iff.mp inside
      linarith
    exact (contained small).2.1.hasFDerivAt
  have secondActual (point : Space) (inside : point ∈ closedBall 0 (outerRadius / 2)) :
      HasFDerivAt firstField (secondField point) point := by
    have small : point ∈ ball 0 outerRadius := by
      apply mem_ball_zero_iff.mpr
      have bound := mem_closedBall_zero_iff.mp inside
      linarith
    exact (contained small).2.2.hasFDerivAt
  have secondLipschitz : LipschitzOnWith constant secondField (closedBall (0 : Space) (outerRadius / 2)) := by
    apply lipschitz.mono
    intro point inside
    apply (contained ?_).1
    apply mem_ball_zero_iff.mpr
    have bound := mem_closedBall_zero_iff.mp inside
    linarith
  refine ⟨outerRadius / 4, by positivity, constant, ?_⟩
  intro base initial final inside
  have baseInside : base ∈ ball 0 (outerRadius / 2) := by
    apply mem_ball_zero_iff.mpr
    have initialNonnegative := norm_nonneg initial
    have finalNonnegative := norm_nonneg final
    linarith
  have secondIdentity : secondField base = quadratic base + (quadratic base).flip := by
    apply ContinuousLinearMap.ext
    intro left
    apply ContinuousLinearMap.ext
    intro right
    have symmetric := second_derivative_symmetric_on_ball function firstField secondField
      0 firstActual secondActual base baseInside left right
    have halfIdentity := eq_half_add_half_of_eq symmetric
    change secondField base left right = quadratic base left right + quadratic base right left
    exact halfIdentity.trans (congrArg₂ (fun initial final : Space => initial + final)
      (quadraticApply base left right).symm (quadraticApply base right left).symm)
  have outerInside : ‖base‖ + (‖initial‖ + ‖final‖) ≤ outerRadius / 2 := by linarith
  exact norm_cubic_taylor_remainder_increment_difference function firstField secondField constant
    firstActual secondActual secondLipschitz base initial final outerInside (quadratic base) secondIdentity

end

end EulerNonuniqueness.General
