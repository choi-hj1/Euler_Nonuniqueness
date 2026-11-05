import EulerNonuniqueness.General.WeightedAngularFluxBound
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open MeasureTheory

namespace MeasureTheory

theorem real_inner_complex_product (first second : ℂ) :
    @inner ℝ ℂ _ first second = (star first * second).re := by
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
  rfl

theorem integral_weighted_angular_strain_difference_le {vorticity : ℂ → ℝ} {velocity : ℂ → ℂ}
    (massIntegrable : Integrable vorticity) (center displacement coefficient : ℂ)
    (firstIntegrable : Integrable (fun position => vorticity position • (position - center)))
    (secondIntegrable : Integrable (fun position => |vorticity position| * ‖position - center‖ ^ 2))
    (complexMomentIntegrable : Integrable (fun position => vorticity position • (position - center) ^ 2))
    (velocityContinuous : Continuous velocity) {error : ℝ} (nonnegative : 0 ≤ error)
    (remainder : ∀ position ∈ Function.support vorticity,
      ‖velocity position - velocity center - coefficient * star (position - center)‖ ≤ error * ‖position - center‖) :
    |(∫ position, @inner ℝ ℂ _ (position - center) (vorticity position • (velocity position - displacement))) -
      (coefficient * star (∫ position, vorticity position • (position - center) ^ 2)).re| ≤
      ‖∫ position, vorticity position • (position - center)‖ * ‖velocity center - displacement‖ +
        error * ∫ position, |vorticity position| * ‖position - center‖ ^ 2 := by
  let residualVelocity : ℂ → ℂ := fun position => velocity position - coefficient * star (position - center)
  have residualContinuous : Continuous residualVelocity := by dsimp only [residualVelocity]; fun_prop
  have residualCenter : residualVelocity center = velocity center := by simp [residualVelocity]
  have residualBound (position : ℂ) (supported : position ∈ Function.support vorticity) :
      ‖residualVelocity position - residualVelocity center‖ ≤ error * ‖position - center‖ := by
    rw [residualCenter]
    have rearrange : residualVelocity position - velocity center =
        velocity position - velocity center - coefficient * star (position - center) := by dsimp only [residualVelocity]; abel
    rw [rearrange]
    exact remainder position supported
  have estimate := abs_integral_weighted_angular_flux_le massIntegrable center displacement firstIntegrable secondIntegrable
    residualContinuous nonnegative residualBound
  rw [residualCenter] at estimate
  let residualFlux : ℂ → ℝ := fun position => @inner ℝ ℂ _ (position - center)
    (vorticity position • (residualVelocity position - displacement))
  have firstNormIntegrable : Integrable (fun position => |vorticity position| * ‖position - center‖) := by
    simpa only [norm_smul, Real.norm_eq_abs] using firstIntegrable.norm
  have domination (position : ℂ) : ‖residualFlux position‖ ≤
      ‖velocity center - displacement‖ * (|vorticity position| * ‖position - center‖) +
        error * (|vorticity position| * ‖position - center‖ ^ 2) := by
    by_cases zero : vorticity position = 0
    · simp only [residualFlux, zero, zero_smul, inner_zero_right, norm_zero, abs_zero, zero_mul, mul_zero, add_zero]
      exact le_rfl
    have split : residualVelocity position - displacement =
        (velocity center - displacement) + (residualVelocity position - residualVelocity center) := by rw [residualCenter]; abel
    have velocityBound : ‖residualVelocity position - displacement‖ ≤
        ‖velocity center - displacement‖ + error * ‖position - center‖ := by
      rw [split]
      exact (norm_add_le _ _).trans (add_le_add_left (residualBound position zero) _)
    calc
      ‖residualFlux position‖ ≤ ‖position - center‖ * ‖vorticity position • (residualVelocity position - displacement)‖ :=
        norm_inner_le_norm _ _
      _ = ‖position - center‖ * (|vorticity position| * ‖residualVelocity position - displacement‖) := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖position - center‖ * (|vorticity position| * (‖velocity center - displacement‖ + error * ‖position - center‖)) := by gcongr
      _ = _ := by ring
  have residualMeasurable : AEStronglyMeasurable residualFlux :=
    (continuous_id.sub continuous_const).aestronglyMeasurable.inner
      (massIntegrable.aestronglyMeasurable.smul (residualContinuous.sub continuous_const).aestronglyMeasurable)
  have residualIntegrable : Integrable residualFlux :=
    ((firstNormIntegrable.const_mul _).add (secondIntegrable.const_mul error)).mono' residualMeasurable
      (Filter.Eventually.of_forall domination)
  have conjugateIntegrable : Integrable (fun position => star (vorticity position • (position - center) ^ 2)) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp complexMomentIntegrable
  have strainIntegrable : Integrable (fun position =>
      (coefficient * star (vorticity position • (position - center) ^ 2)).re) :=
    (conjugateIntegrable.const_mul coefficient).re
  have decomposition (position : ℂ) :
      @inner ℝ ℂ _ (position - center) (vorticity position • (velocity position - displacement)) =
        residualFlux position + (coefficient * star (vorticity position • (position - center) ^ 2)).re := by
    dsimp only [residualFlux, residualVelocity]
    simp only [real_inner_complex_product, Complex.smul_re, Complex.smul_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re, Complex.conj_im, pow_two]
    simp only [smul_eq_mul]
    ring
  have leadingIntegral : (∫ position, (coefficient * star (vorticity position • (position - center) ^ 2)).re) =
      (coefficient * star (∫ position, vorticity position • (position - center) ^ 2)).re := by
    change (∫ position, RCLike.re (coefficient * star (vorticity position • (position - center) ^ 2))) = _
    rw [integral_re (conjugateIntegrable.const_mul coefficient)]
    change (∫ position, coefficient * star (vorticity position • (position - center) ^ 2)).re = _
    rw [integral_const_mul]
    have conjugateIdentity : (∫ position, star (vorticity position • (position - center) ^ 2)) =
        star (∫ position, vorticity position • (position - center) ^ 2) := integral_conj
    rw [conjugateIdentity]
  have integralDecomposition :
      (∫ position, @inner ℝ ℂ _ (position - center) (vorticity position • (velocity position - displacement))) =
        (∫ position, residualFlux position) +
          (coefficient * star (∫ position, vorticity position • (position - center) ^ 2)).re := by
    simp_rw [decomposition]
    rw [integral_add residualIntegrable strainIntegrable, leadingIntegral]
  rw [integralDecomposition, add_sub_cancel_right]
  exact estimate

end MeasureTheory
