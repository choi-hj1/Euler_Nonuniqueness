import EulerNonuniqueness.General.ComplexPhaseLift
import EulerNonuniqueness.Section4.ReferencePaperShapeRegularity
import EulerNonuniqueness.Section4.ReferenceInitialShapeCoordinates

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem initialPositiveDiagonal_polar (scales : Scales) (index : ℕ) (phase unstable : ℝ) :
    initialPositiveDiagonal scales index phase unstable =
      (‖initialPositiveDiagonal scales index phase unstable‖ : ℂ) * Complex.exp (Complex.I * (phase : ℂ)) := by
  let factor := scales.length index / Real.sqrt (1 - rhombusRatio * (1 + unstable))
  have factorNonnegative : 0 ≤ factor := div_nonneg (scales.length_pos index).le (Real.sqrt_nonneg _)
  have identity : initialPositiveDiagonal scales index phase unstable =
      (factor : ℂ) * Complex.exp (Complex.I * (phase : ℂ)) := by
    dsimp only [initialPositiveDiagonal, factor]
    rw [Complex.ofReal_div]
    ring
  have rotationNorm : ‖Complex.exp (Complex.I * (phase : ℂ))‖ = 1 := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, Real.exp_zero]
  have normIdentity : ‖initialPositiveDiagonal scales index phase unstable‖ = factor := by
    rw [identity, norm_mul, rotationNorm, mul_one, Complex.norm_real, Real.norm_of_nonneg factorNonnegative]
  rw [normIdentity]
  exact identity

theorem FiniteMovingPatchFamily.exists_reference_phaseLift {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {threshold : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion 2)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) {phase unstable : Fin count → ℝ}
    (initial : ReferenceInitialDisks scales family.patchMotion phase unstable threshold)
    (inside : ∀ time ∈ Icc 0 2, ∀ index,
      time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (differenceLower : ∀ time ∈ Icc 0 2, ∀ index : Fin count,
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index) :
    ∃ phaseLift : ℝ → Fin count → ℝ,
      ReferencePhaseLift family.patchMotion phase phaseLift ∧
        ∀ index time, time ∈ Icc 0 2 →
          HasDerivAt (fun current => phaseLift current index)
            (deriv (fun current => positiveHalfDiagonal family.patchMotion current index) time /
              positiveHalfDiagonal family.patchMotion time index).im time := by
  have phaseExists (index : Fin count) : ∃ lift : ℝ → ℝ, Continuous lift ∧ lift 0 = phase index ∧
      ∀ time ∈ Icc 0 2,
        HasDerivAt lift (deriv (fun current => positiveHalfDiagonal family.patchMotion current index) time /
          positiveHalfDiagonal family.patchMotion time index).im time ∧
        positiveHalfDiagonal family.patchMotion time index =
          (‖positiveHalfDiagonal family.patchMotion time index‖ : ℂ) * Complex.exp (Complex.I * (lift time : ℂ)) := by
    have regularity (time : ℝ) (member : time ∈ Icc 0 2) :=
      (family.halfDiagonals_contDiffAt index (fun patch => inside time member (finProdFinEquiv (index, patch)))).1
    have derivativeContinuous : ContinuousOn (deriv (fun current => positiveHalfDiagonal family.patchMotion current index)) (Icc 0 2) := by
      intro time member
      have derivativeAt : ContinuousAt (fderiv ℝ (fun current => positiveHalfDiagonal family.patchMotion current index)) time :=
        ((regularity time member).fderiv_right (m := 0) (by norm_num)).continuousAt
      exact ((ContinuousLinearMap.apply ℝ ℂ (1 : ℝ)).continuous.continuousAt.comp derivativeAt).continuousWithinAt
    have nonzero (time : ℝ) (member : time ∈ Icc 0 2) : positiveHalfDiagonal family.patchMotion time index ≠ 0 := by
      intro zero
      have lower := differenceLower time member index
      dsimp only [diagonalDifference] at lower
      rw [zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub] at lower
      nlinarith [sq_pos_of_pos (scales.length_pos (index.val + 1)), sq_nonneg ‖negativeHalfDiagonal family.patchMotion time index‖]
    have initialPolar : positiveHalfDiagonal family.patchMotion 0 index =
        (‖positiveHalfDiagonal family.patchMotion 0 index‖ : ℂ) * Complex.exp (Complex.I * (phase index : ℂ)) := by
      rw [(evolution.reference_initial_diagonals (by norm_num) amplitudePositive frequencyPositive ratioPositive initial index).1]
      exact initialPositiveDiagonal_polar scales _ _ _
    exact EulerNonuniqueness.General.exists_complex_phase_on_Icc (by norm_num)
      (fun time member => (regularity time member).differentiableAt (by norm_num) |>.hasDerivAt)
      derivativeContinuous nonzero initialPolar
  choose lift continuous initialValue properties using phaseExists
  refine ⟨fun time index => lift index time, ?_, ?_⟩
  · intro index
    exact ⟨(continuous index).continuousOn, initialValue index, fun time member => (properties index time member).2⟩
  · intro index time member
    exact (properties index time member).1

end EulerNonuniqueness.Paper
