import EulerNonuniqueness.Section4.ReferenceConstructedPhaseLift

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

def referenceDilation {count : ℕ} (scales : Scales) (motion : PatchMotion count) (index : Fin count) (time : ℝ) : ℝ :=
  diagonalDifference motion time index / scales.length (index.val + 1) ^ 2

def referencePhaseError {count : ℕ} (scales : Scales) (motion : PatchMotion count) (index : Fin count) (time : ℝ) : ℝ :=
  (deriv (fun current => positiveHalfDiagonal motion current index) time / positiveHalfDiagonal motion time index).im +
    scales.omega (index.val + 1) / referenceDilation scales motion index time

namespace FiniteMovingPatchFamily

theorem referenceDilation_contDiffAt {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (scales : Scales) (index : Fin count) {time : ℝ}
    (inside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime) :
    ContDiffAt ℝ 1 (referenceDilation scales family.patchMotion index) time := by
  obtain ⟨positive, negative⟩ := family.halfDiagonals_contDiffAt index inside
  have positiveNorm := (contDiff_norm_sq ℝ).contDiffAt.comp time positive
  have negativeNorm := (contDiff_norm_sq ℝ).contDiffAt.comp time negative
  exact (positiveNorm.sub negativeNorm).div_const _

theorem referenceDilation_deriv_continuousOn {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (scales : Scales) (index : Fin count) (times : Set ℝ)
    (inside : ∀ time ∈ times, ∀ patch : Fin 4,
      time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
        (family.patch (finProdFinEquiv (index, patch))).finalTime) :
    ContinuousOn (deriv (referenceDilation scales family.patchMotion index)) times := by
  intro time member
  have smooth := family.referenceDilation_contDiffAt scales index (inside time member)
  have differentialContinuous := (smooth.fderiv_right (m := 0) (by norm_num)).continuousAt
  exact ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).continuous.continuousAt.comp differentialContinuous).continuousWithinAt

theorem referencePhaseError_continuousOn {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (scales : Scales) (index : Fin count) (times : Set ℝ)
    (inside : ∀ time ∈ times, ∀ patch : Fin 4,
      time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
        (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (positiveNonzero : ∀ time ∈ times, positiveHalfDiagonal family.patchMotion time index ≠ 0)
    (dilationNonzero : ∀ time ∈ times, referenceDilation scales family.patchMotion index time ≠ 0) :
    ContinuousOn (referencePhaseError scales family.patchMotion index) times := by
  intro time member
  have positiveSmooth := (family.halfDiagonals_contDiffAt index (inside time member)).1
  have derivativeContinuous := (positiveSmooth.fderiv_right (m := 0) (by norm_num)).continuousAt
  have positiveDerivativeContinuous : ContinuousWithinAt
      (deriv (fun current => positiveHalfDiagonal family.patchMotion current index)) times time :=
    ((ContinuousLinearMap.apply ℝ ℂ (1 : ℝ)).continuous.continuousAt.comp derivativeContinuous).continuousWithinAt
  have quotient := positiveDerivativeContinuous.div positiveSmooth.continuousAt.continuousWithinAt (positiveNonzero time member)
  have first := Complex.continuous_im.continuousAt.comp_continuousWithinAt quotient
  have second : ContinuousWithinAt (fun current => scales.omega (index.val + 1) /
      referenceDilation scales family.patchMotion index current) times time := continuousWithinAt_const.div
    (family.referenceDilation_contDiffAt scales index (inside time member)).continuousAt.continuousWithinAt (dilationNonzero time member)
  exact first.add second

theorem exists_reference_phase_on_prefix {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    {scales : Scales} {horizon finish threshold : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (horizonPositive : 0 < horizon) (finishNonnegative : 0 ≤ finish)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {phase unstable : Fin count → ℝ} (initial : ReferenceInitialDisks scales family.patchMotion phase unstable threshold)
    (inside : ∀ time ∈ Icc 0 finish, ∀ source,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (differenceLower : ∀ time ∈ Icc 0 finish, ∀ index : Fin count,
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index)
    (index : Fin count) :
    ∃ lift : ℝ → ℝ, Continuous lift ∧ lift 0 = phase index ∧
      ∀ time ∈ Icc 0 finish,
        HasDerivAt lift (-scales.omega (index.val + 1) / referenceDilation scales family.patchMotion index time +
          referencePhaseError scales family.patchMotion index time) time ∧
        positiveHalfDiagonal family.patchMotion time index =
          (‖positiveHalfDiagonal family.patchMotion time index‖ : ℂ) * Complex.exp (Complex.I * (lift time : ℂ)) := by
  have regularity (time : ℝ) (member : time ∈ Icc 0 finish) :=
    (family.halfDiagonals_contDiffAt index (fun patch => inside time member (finProdFinEquiv (index, patch)))).1
  have derivativeContinuous : ContinuousOn (deriv (fun current => positiveHalfDiagonal family.patchMotion current index)) (Icc 0 finish) := by
    intro time member
    have differentialContinuous := ((regularity time member).fderiv_right (m := 0) (by norm_num)).continuousAt
    exact ((ContinuousLinearMap.apply ℝ ℂ (1 : ℝ)).continuous.continuousAt.comp differentialContinuous).continuousWithinAt
  have nonzero (time : ℝ) (member : time ∈ Icc 0 finish) : positiveHalfDiagonal family.patchMotion time index ≠ 0 := by
    intro zero
    have lower := differenceLower time member index
    dsimp only [diagonalDifference] at lower
    rw [zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub] at lower
    nlinarith [sq_pos_of_pos (scales.length_pos (index.val + 1)), sq_nonneg ‖negativeHalfDiagonal family.patchMotion time index‖]
  have initialPolar : positiveHalfDiagonal family.patchMotion 0 index =
      (‖positiveHalfDiagonal family.patchMotion 0 index‖ : ℂ) * Complex.exp (Complex.I * (phase index : ℂ)) := by
    rw [(evolution.reference_initial_diagonals horizonPositive.le amplitudePositive frequencyPositive ratioPositive initial index).1]
    exact initialPositiveDiagonal_polar scales _ _ _
  obtain ⟨lift, continuous, initialValue, properties⟩ := General.exists_complex_phase_on_Icc finishNonnegative
    (fun time member => (regularity time member).differentiableAt (by norm_num) |>.hasDerivAt)
    derivativeContinuous nonzero initialPolar
  refine ⟨lift, continuous, initialValue, ?_⟩
  intro time member
  have identity : -scales.omega (index.val + 1) / referenceDilation scales family.patchMotion index time +
      referencePhaseError scales family.patchMotion index time =
      (deriv (fun current => positiveHalfDiagonal family.patchMotion current index) time /
        positiveHalfDiagonal family.patchMotion time index).im := by unfold referencePhaseError; ring
  rw [identity]
  exact properties time member

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
