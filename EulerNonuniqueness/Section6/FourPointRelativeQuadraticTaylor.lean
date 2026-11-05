import EulerNonuniqueness.Section6.FullPointShapeDynamics
import EulerNonuniqueness.General.RelativeQuadraticTaylorUniform

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem fourPointField_contDiffAt_three (coefficient : ℝ) {positions : FourPointConfiguration}
    (noncollision : FourPointNoncollision positions) : ContDiffAt ℝ 3 (fourPointField coefficient) positions := by
  apply contDiffAt_pi.mpr
  intro target
  unfold fourPointField
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro source _
  by_cases same : source = target
  · simp only [same, if_true]
    exact contDiffAt_const
  · simp only [same, if_false]
    have difference : ContDiffAt ℝ 3
        (fun current : FourPointConfiguration => current target - current source) positions := by fun_prop
    have conjugate : ContDiffAt ℝ 3
        (fun current : FourPointConfiguration => star (current target - current source)) positions :=
      Complex.conjCLE.contDiff.contDiffAt.comp positions difference
    simpa only [div_eq_mul_inv] using
      contDiffAt_const.mul (conjugate.inv (star_ne_zero.mpr (noncollision target source same)))

theorem fourPointField_uniform_relative_quadratic_remainder {base : FourPointConfiguration}
    (noncollision : FourPointNoncollision base) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ first second firstIncrement secondIncrement : FourPointConfiguration,
      FourPointNoncollision first → FourPointNoncollision second →
      ‖first - base‖ + (‖firstIncrement‖ + ‖secondIncrement‖) ≤ radius →
      ‖second - base‖ + (‖firstIncrement‖ + ‖secondIncrement‖) ≤ radius →
      ‖(fourPointField coefficient (first + firstIncrement) - fourPointField coefficient first -
          fourPointLinearization coefficient first firstIncrement) -
        (fourPointField coefficient (second + secondIncrement) - fourPointField coefficient second -
          fourPointLinearization coefficient second secondIncrement)‖ ≤
        bound * |coefficient| * ((‖firstIncrement‖ + ‖secondIncrement‖) * ‖firstIncrement - secondIncrement‖ +
          ‖first - second‖ * ‖secondIncrement‖ ^ 2) := by
  let function : FourPointConfiguration → FourPointConfiguration := fun state => fourPointField 1 (base + state)
  have smooth : ContDiffAt ℝ 3 function 0 := by
    have outer : ContDiffAt ℝ 3 (fourPointField 1) (base + (0 : FourPointConfiguration)) := by
      simpa only [add_zero] using fourPointField_contDiffAt_three 1 noncollision
    exact outer.comp (0 : FourPointConfiguration) (contDiffAt_const.add contDiffAt_id)
  have regular : EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear function 0 :=
    ⟨EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_contDiffAt_two (smooth.of_le (by decide)),
      EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_contDiffAt_two
        (smooth.fderiv_right (by norm_num))⟩
  obtain ⟨radius, positive, bound, estimate⟩ :=
    EulerNonuniqueness.General.exists_relative_quadratic_taylor_ball function regular
  refine ⟨bound, bound.coe_nonneg, radius, positive, ?_⟩
  intro coefficient first second firstIncrement secondIncrement firstNoncollision secondNoncollision firstSmall secondSmall
  have derivative (positions increment : FourPointConfiguration) (collision : FourPointNoncollision positions) :
      fderiv ℝ function (positions - base) increment = fourPointLinearization 1 positions increment := by
    have shift : HasFDerivAt (fun state : FourPointConfiguration => base + state)
        (ContinuousLinearMap.id ℝ FourPointConfiguration) (positions - base) := (hasFDerivAt_id _).const_add base
    have outer := (fourPointField_contDiffAt 1 collision).differentiableAt (by norm_num)
    have identity : base + (positions - base) = positions := by abel
    have shiftedOuter : HasFDerivAt (fourPointField 1) (fderiv ℝ (fourPointField 1) positions)
        (base + (positions - base)) := by
      rw [identity]
      exact outer.hasFDerivAt
    have actual := shiftedOuter.comp (positions - base) shift
    have actual' : HasFDerivAt function (fderiv ℝ (fourPointField 1) positions) (positions - base) := by
      simpa only [function, Function.comp_def, ContinuousLinearMap.comp_id] using actual
    rw [actual'.fderiv]
    exact fourPointField_fderiv 1 collision increment
  have actual := estimate (first - base) (second - base) firstIncrement secondIncrement firstSmall secondSmall
  rw [derivative first firstIncrement firstNoncollision, derivative second secondIncrement secondNoncollision] at actual
  have firstIdentity : base + (first - base + firstIncrement) = first + firstIncrement := by abel
  have secondIdentity : base + (second - base + secondIncrement) = second + secondIncrement := by abel
  have baseFirst : base + (first - base) = first := by abel
  have baseSecond : base + (second - base) = second := by abel
  have difference : first - base - (second - base) = first - second := by abel
  dsimp only [function] at actual
  rw [firstIdentity, secondIdentity, baseFirst, baseSecond, difference] at actual
  have scaleIdentity :
      (fourPointField coefficient (first + firstIncrement) - fourPointField coefficient first -
          fourPointLinearization coefficient first firstIncrement) -
        (fourPointField coefficient (second + secondIncrement) - fourPointField coefficient second -
          fourPointLinearization coefficient second secondIncrement) =
      coefficient • ((fourPointField 1 (first + firstIncrement) - fourPointField 1 first -
          fourPointLinearization 1 first firstIncrement) -
        (fourPointField 1 (second + secondIncrement) - fourPointField 1 second -
          fourPointLinearization 1 second secondIncrement)) := by
    rw [fourPointField_scaling coefficient, fourPointField_scaling coefficient,
      fourPointField_scaling coefficient, fourPointField_scaling coefficient,
      fourPointLinearization_scaling coefficient, fourPointLinearization_scaling coefficient,
      smul_sub, smul_sub, smul_sub, smul_sub, smul_sub]
  rw [scaleIdentity, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left actual (abs_nonneg coefficient)).trans_eq (by ring)

end EulerNonuniqueness.Section6
