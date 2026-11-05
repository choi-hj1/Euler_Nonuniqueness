import EulerNonuniqueness.Section6.SourceMomentStrainError
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

def rhombusConstantMomentInput (positive : ℝ → ℂ) (moment displacement : ℂ) (time : ℝ) : ℝ :=
  let negative := Complex.I * (Real.sqrt Section2.rhombusRatio : ℂ) * positive time
  let strain := -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * moment / displacement ^ 4)
  (pointShapeForcing (positive time) negative (strain * star (positive time)) (strain * star negative)).1

theorem rhombusConstantMomentInput_continuous {positive : ℝ → ℂ}
    (continuous : Continuous positive) (nonzero : ∀ time, positive time ≠ 0) (moment displacement : ℂ) :
    Continuous (rhombusConstantMomentInput positive moment displacement) := by
  have identity : rhombusConstantMomentInput positive moment displacement = fun time =>
      -2 * ((-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * moment / displacement ^ 4)) *
        star (positive time) / positive time).re -
      Real.sqrt 2 * ((-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * moment / displacement ^ 4)) *
        star (positive time) / positive time).im := by
    funext time
    exact congrArg Prod.fst (pointShapeForcing_rhombus (nonzero time) _)
  rw [identity]
  have logarithmic : Continuous (fun time =>
      (-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * moment / displacement ^ 4)) *
        star (positive time) / positive time) :=
    (continuous_const.mul continuous.star).div₀ continuous nonzero
  exact (continuous_const.mul (Complex.continuous_re.comp logarithmic)).sub
    (continuous_const.mul (Complex.continuous_im.comp logarithmic))

theorem rhombusConstantMomentInput_abs_bound {positive : ℝ → ℂ}
    (nonzero : ∀ time, positive time ≠ 0) (moment displacement : ℂ) (time : ℝ) :
    |rhombusConstantMomentInput positive moment displacement time| ≤
      6 * ‖moment‖ / (Real.pi * ‖displacement‖ ^ 4) := by
  have estimate := rhombus_unstable_strain_lipschitz (nonzero time)
    (-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * moment / displacement ^ 4)) 0
  simp only [zero_mul, pointShapeForcing, zero_div, sub_self, Complex.zero_re, Complex.zero_im,
    mul_zero, zero_add, div_self, sub_zero] at estimate
  change |rhombusConstantMomentInput positive moment displacement time| ≤ _ at estimate
  convert estimate using 1
  simp only [norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (show 0 < 2 * Real.pi by positivity), norm_star, norm_pow]
  norm_num
  rw [abs_of_pos Real.pi_pos]
  ring

theorem rhombusConstantMomentInput_weighted_bound {positive : ℝ → ℂ}
    (continuous : Continuous positive) (nonzero : ∀ time, positive time ≠ 0)
    (moment displacement : ℂ) {decay : ℝ} (decayPositive : 0 < decay) :
    IntegrableOn (fun time => Real.exp (-decay * time) *
      rhombusConstantMomentInput positive moment displacement time) (Ioi 0) ∧
    |∫ time in Ioi 0, Real.exp (-decay * time) *
      rhombusConstantMomentInput positive moment displacement time| ≤
        6 * ‖moment‖ / (Real.pi * ‖displacement‖ ^ 4 * decay) := by
  let bound := 6 * ‖moment‖ / (Real.pi * ‖displacement‖ ^ 4)
  have boundNonnegative : 0 ≤ bound := by dsimp only [bound]; positivity
  have dominator : IntegrableOn (fun time => Real.exp (-decay * time) * bound) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -decay < 0) 0).mul_const bound
  have estimate (time : ℝ) : ‖Real.exp (-decay * time) *
      rhombusConstantMomentInput positive moment displacement time‖ ≤ Real.exp (-decay * time) * bound := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (rhombusConstantMomentInput_abs_bound nonzero moment displacement time)
      (Real.exp_pos _).le
  have measurable : AEStronglyMeasurable (fun time => Real.exp (-decay * time) *
      rhombusConstantMomentInput positive moment displacement time) (volume.restrict (Ioi 0)) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (rhombusConstantMomentInput_continuous continuous nonzero moment displacement)).aestronglyMeasurable
  have integrable := dominator.mono' measurable (Filter.Eventually.of_forall estimate)
  refine ⟨integrable, ?_⟩
  calc
    _ ≤ ∫ time in Ioi 0, ‖Real.exp (-decay * time) *
        rhombusConstantMomentInput positive moment displacement time‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ time in Ioi 0, Real.exp (-decay * time) * bound :=
      integral_mono integrable.norm dominator estimate
    _ = _ := by
      rw [integral_mul_const, integral_exp_mul_Ioi (by linarith : -decay < 0) 0]
      simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
      dsimp only [bound]
      ring

end EulerNonuniqueness.Section6
