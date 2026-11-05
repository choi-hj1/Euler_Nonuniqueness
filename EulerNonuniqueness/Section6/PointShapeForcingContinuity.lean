import EulerNonuniqueness.Section6.FullPointShapeDynamics

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem pointShapeForcing_continuousOn {times : Set ℝ}
    {positive negative positiveForcing negativeForcing : ℝ → ℂ}
    (positiveContinuous : ContinuousOn positive times)
    (negativeContinuous : ContinuousOn negative times)
    (positiveForcingContinuous : ContinuousOn positiveForcing times)
    (negativeForcingContinuous : ContinuousOn negativeForcing times)
    (positiveNonzero : ∀ time ∈ times, positive time ≠ 0)
    (negativeNonzero : ∀ time ∈ times, negative time ≠ 0) :
    ContinuousOn (fun time => pointShapeForcing (positive time) (negative time)
      (positiveForcing time) (negativeForcing time)) times := by
  have difference := (negativeForcingContinuous.div negativeContinuous negativeNonzero).sub
    (positiveForcingContinuous.div positiveContinuous positiveNonzero)
  have ratio : ContinuousOn (fun time => pointShapeRatio (positive time) (negative time)) times :=
    (negativeContinuous.norm.pow 2).div (positiveContinuous.norm.pow 2)
      (fun time member => pow_ne_zero 2 (norm_ne_zero_iff.mpr (positiveNonzero time member)))
  have realPart := Complex.continuous_re.comp_continuousOn difference
  have imaginaryPart := Complex.continuous_im.comp_continuousOn difference
  unfold pointShapeForcing
  exact ((((continuousOn_const.mul ratio).mul realPart).div_const _).add
    ((continuousOn_const.mul imaginaryPart).div_const _)).div_const _ |>.prodMk
    (((((continuousOn_const.mul ratio).mul realPart).div_const _).sub
      ((continuousOn_const.mul imaginaryPart).div_const _)).div_const _)

theorem pointVelocities_continuousOn (coefficient : ℝ) {times : Set ℝ}
    {positive negative : ℝ → ℂ}
    (positiveContinuous : ContinuousOn positive times)
    (negativeContinuous : ContinuousOn negative times)
    (positiveNonzero : ∀ time ∈ times, positive time ≠ 0)
    (negativeNonzero : ∀ time ∈ times, negative time ≠ 0)
    (squaresNonzero : ∀ time ∈ times, star (positive time) ^ 2 - star (negative time) ^ 2 ≠ 0) :
    ContinuousOn (fun time => positivePointVelocity coefficient (positive time) (negative time)) times ∧
      ContinuousOn (fun time => negativePointVelocity coefficient (positive time) (negative time)) times := by
  have positiveStar := continuous_star.comp_continuousOn positiveContinuous
  have negativeStar := continuous_star.comp_continuousOn negativeContinuous
  have difference := (positiveStar.pow 2).sub (negativeStar.pow 2)
  constructor
  · unfold positivePointVelocity
    exact (continuousOn_const.mul ((continuousOn_const.mul (positiveStar.pow 2)).add (negativeStar.pow 2))).div
      ((continuousOn_const.mul positiveStar).mul difference)
      (fun time member => mul_ne_zero (mul_ne_zero (by norm_num) (star_ne_zero.mpr (positiveNonzero time member)))
        (squaresNonzero time member))
  · unfold negativePointVelocity
    exact (continuousOn_const.mul ((positiveStar.pow 2).add (continuousOn_const.mul (negativeStar.pow 2)))).div
      ((continuousOn_const.mul negativeStar).mul difference)
      (fun time member => mul_ne_zero (mul_ne_zero (by norm_num) (star_ne_zero.mpr (negativeNonzero time member)))
        (squaresNonzero time member))

end EulerNonuniqueness.Section6
