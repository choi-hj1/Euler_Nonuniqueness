import Mathlib

noncomputable section

open Set MeasureTheory

namespace intervalIntegral

theorem integral_exp_neg_mul_le_of_affine_majorant
    {function : ℝ → ℝ} {weight slope constant origin start finish : ℝ}
    (regular : ContinuousOn function (Icc start finish))
    (weightPositive : 0 < weight) (slopeNonnegative : 0 ≤ slope)
    (constantNonnegative : 0 ≤ constant) (originBound : origin ≤ start) (ordered : start ≤ finish)
    (majorized : ∀ time ∈ Icc start finish, function time ≤ slope * (time - origin) + constant) :
    IntervalIntegrable (fun time => Real.exp (-weight * (time - start)) * function time) volume start finish ∧
    (∫ time in start..finish, Real.exp (-weight * (time - start)) * function time) ≤
      slope / weight ^ 2 + (slope * (start - origin) + constant) / weight := by
  let primitive := fun time => -(Real.exp (-weight * (time - start)) *
    (slope * (weight * (time - origin) + 1) + constant * weight)) / weight ^ 2
  have derivative (time : ℝ) : HasDerivAt primitive
      (Real.exp (-weight * (time - start)) * (slope * (time - origin) + constant)) time := by
    have exponential := ((((hasDerivAt_id time).sub_const start).const_mul (-weight)).exp)
    have linear := (((((hasDerivAt_id time).sub_const origin).const_mul weight).add_const 1).const_mul slope).add_const (constant * weight)
    convert (exponential.mul linear).neg.div_const (weight ^ 2) using 1
    dsimp only
    field_simp [weightPositive.ne']
    ring
  have exponentialContinuous : Continuous (fun time : ℝ => Real.exp (-weight * (time - start))) := by fun_prop
  have weightedIntegrable := (exponentialContinuous.continuousOn.mul regular).intervalIntegrable_of_Icc
    (μ := volume) ordered
  have affineContinuous : Continuous (fun time : ℝ =>
      Real.exp (-weight * (time - start)) * (slope * (time - origin) + constant)) := by fun_prop
  have affineIntegrable := affineContinuous.intervalIntegrable (μ := volume) start finish
  have affineIdentity := integral_eq_sub_of_hasDerivAt (fun time _ => derivative time) affineIntegrable
  have initial : primitive start = -(slope / weight ^ 2 + (slope * (start - origin) + constant) / weight) := by
    dsimp only [primitive]
    simp only [sub_self, mul_zero, Real.exp_zero, one_mul]
    field_simp [weightPositive.ne']
    ring
  have terminal : primitive finish ≤ 0 := by
    have elapsedNonnegative : 0 ≤ finish - origin := sub_nonneg.mpr (originBound.trans ordered)
    dsimp only [primitive]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr
      (mul_nonneg (Real.exp_pos _).le (add_nonneg
        (mul_nonneg slopeNonnegative (by positivity)) (mul_nonneg constantNonnegative weightPositive.le))))
      (sq_nonneg weight)
  have integrated := integral_mono_on ordered weightedIntegrable affineIntegrable
    (fun time inside => mul_le_mul_of_nonneg_left (majorized time inside) (Real.exp_pos _).le)
  rw [affineIdentity, initial] at integrated
  exact ⟨weightedIntegrable, by linarith only [integrated, terminal]⟩

end intervalIntegral
