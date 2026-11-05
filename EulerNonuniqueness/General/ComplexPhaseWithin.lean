import EulerNonuniqueness.General.ODEPrimitiveExtension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open Set

namespace EulerNonuniqueness.General

private theorem complex_polar_product_exp (initial increment : ℂ) (phase : ℝ)
    (initialEquation : initial = (‖initial‖ : ℂ) * Complex.exp (Complex.I * (phase : ℂ))) :
    initial * Complex.exp increment = (‖initial * Complex.exp increment‖ : ℂ) *
      Complex.exp (Complex.I * ((phase + increment.im : ℝ) : ℂ)) := by
  have split : Complex.exp increment = (Real.exp increment.re : ℂ) *
      Complex.exp (Complex.I * (increment.im : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp
  calc
    initial * Complex.exp increment = ((‖initial‖ : ℂ) * Complex.exp (Complex.I * (phase : ℂ))) *
        ((Real.exp increment.re : ℂ) * Complex.exp (Complex.I * (increment.im : ℂ))) :=
      congrArg₂ (fun first second : ℂ => first * second) initialEquation split
    _ = ((‖initial‖ : ℂ) * (Real.exp increment.re : ℂ)) *
        Complex.exp (Complex.I * ((phase + increment.im : ℝ) : ℂ)) := by
      rw [Complex.ofReal_add, mul_add, Complex.exp_add]
      ring
    _ = _ := by rw [norm_mul, Complex.norm_exp, Complex.ofReal_mul]

private theorem integrating_factor_hasDerivWithinAt {path primitive : ℝ → ℂ} {velocity : ℂ} {time : ℝ} {times : Set ℝ}
    (pathEquation : HasDerivWithinAt path velocity times time)
    (primitiveEquation : HasDerivWithinAt primitive (velocity / path time) times time)
    (nonzero : path time ≠ 0) :
    HasDerivWithinAt (fun current => path current * Complex.exp (-(primitive current))) 0 times time := by
  have actual := pathEquation.mul primitiveEquation.neg.cexp
  convert actual using 1
  field_simp [nonzero]
  ring

theorem exists_complex_phase_on_Icc_of_within_derivative {path velocity : ℝ → ℂ} {horizon initialPhase : ℝ}
    (horizonNonnegative : 0 ≤ horizon)
    (equation : ∀ time ∈ Icc 0 horizon, HasDerivWithinAt path (velocity time) (Icc 0 horizon) time)
    (velocityContinuous : ContinuousOn velocity (Icc 0 horizon))
    (nonzero : ∀ time ∈ Icc 0 horizon, path time ≠ 0)
    (initialEquation : path 0 = (‖path 0‖ : ℂ) * Complex.exp (Complex.I * (initialPhase : ℂ))) :
    ∃ phase : ℝ → ℝ, Continuous phase ∧ phase 0 = initialPhase ∧
      ∀ time ∈ Icc 0 horizon, HasDerivAt phase (velocity time / path time).im time ∧
        path time = (‖path time‖ : ℂ) * Complex.exp (Complex.I * (phase time : ℂ)) := by
  have pathContinuous : ContinuousOn path (Icc 0 horizon) :=
    fun time member => (equation time member).continuousWithinAt
  have quotientContinuous := velocityContinuous.div pathContinuous nonzero
  let rate : ℝ → ℂ := fun time => velocity (projIcc 0 horizon horizonNonnegative time) /
    path (projIcc 0 horizon horizonNonnegative time)
  have rateContinuous : Continuous rate :=
    (continuousOn_iff_continuous_restrict.mp quotientContinuous).comp continuous_projIcc
  have rateAgreement (time : ℝ) (member : time ∈ Icc 0 horizon) : rate time = velocity time / path time := by
    simp only [rate, projIcc_of_mem horizonNonnegative member]
  let primitive := odePrimitiveExtension (fun _ : ℝ => (0 : ℂ)) rate
  have primitiveEquation (time : ℝ) : HasDerivAt primitive (rate time) time :=
    odePrimitiveExtension_hasDerivAt _ _ rateContinuous time
  have primitiveContinuous : Continuous primitive := odePrimitiveExtension_continuous _ _ rateContinuous
  have primitiveInitial : primitive 0 = 0 := odePrimitiveExtension_initial _ _
  let phase : ℝ → ℝ := fun time => initialPhase + (primitive time).im
  have phaseContinuous : Continuous phase := continuous_const.add (Complex.continuous_im.comp primitiveContinuous)
  have phaseInitial : phase 0 = initialPhase := by simp only [phase, primitiveInitial, Complex.zero_im, add_zero]
  let transformed : ℝ → ℂ := fun time => path time * Complex.exp (-(primitive time))
  have transformedEquation (time : ℝ) (member : time ∈ Icc 0 horizon) : HasDerivWithinAt transformed 0 (Icc 0 horizon) time := by
    apply integrating_factor_hasDerivWithinAt (equation time member) _ (nonzero time member)
    simpa only [rateAgreement time member] using (primitiveEquation time).hasDerivWithinAt
  have transformedInitial : transformed 0 = path 0 := by
    simp only [transformed, primitiveInitial, neg_zero, Complex.exp_zero, mul_one]
  have transformedConstant (time : ℝ) (member : time ∈ Icc 0 horizon) : transformed time = path 0 := by
    have estimate := norm_image_sub_le_of_norm_deriv_le_segment' (C := 0)
      (fun current currentInside => transformedEquation current currentInside)
      (fun _ _ => by simp only [norm_zero, le_refl]) time member
    have zero : ‖transformed time - transformed 0‖ = 0 := by
      apply le_antisymm _ (norm_nonneg _)
      simpa only [zero_mul] using estimate
    exact (sub_eq_zero.mp (norm_eq_zero.mp zero)).trans transformedInitial
  refine ⟨phase, phaseContinuous, phaseInitial, ?_⟩
  intro time member
  constructor
  · have actual := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt time (primitiveEquation time)).const_add initialPhase
    simpa only [Complex.imCLM_apply, rateAgreement time member] using actual
  · have representation : path time = path 0 * Complex.exp (primitive time) := by
      have multiplied := congrArg (fun value : ℂ => value * Complex.exp (primitive time)) (transformedConstant time member)
      simpa only [transformed, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one] using multiplied
    have polar := complex_polar_product_exp (path 0) (primitive time) initialPhase initialEquation
    rw [← representation] at polar
    exact polar

end EulerNonuniqueness.General

