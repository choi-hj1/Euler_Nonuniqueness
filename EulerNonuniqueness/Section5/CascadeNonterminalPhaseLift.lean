import EulerNonuniqueness.Section5.CascadeNonterminalInitialMoments
import EulerNonuniqueness.Section4.ReferencePhaseKinematics

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.CascadeMaterialPreparedPair

theorem nonterminal_exists_phase_on_prefix
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (index : Fin count) (nonterminal : index.val + 1 < count)
    {finish : ℝ} (finishNonnegative : 0 ≤ finish)
    (inside : ∀ time ∈ Icc 0 finish, ∀ source,
      time ∈ Ioo (prepared.trajectory.movingFamily.patch source).initialTime
        (prepared.trajectory.movingFamily.patch source).finalTime)
    (differencePositive : ∀ time ∈ Icc 0 finish,
      0 < diagonalDifference prepared.trajectory.movingFamily.patchMotion time index) :
    ∃ lift : ℝ → ℝ, Continuous lift ∧ lift 0 = phase (index.val + 1) ∧
      ∀ time ∈ Icc 0 finish,
        HasDerivAt lift (-scales.omega (index.val + 1) /
          referenceDilation scales prepared.trajectory.movingFamily.patchMotion index time +
          referencePhaseError scales prepared.trajectory.movingFamily.patchMotion index time) time ∧
        positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index =
          (‖positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift time : ℂ)) := by
  let family := prepared.trajectory.movingFamily
  have regularity (time : ℝ) (member : time ∈ Icc 0 finish) :=
    (family.halfDiagonals_contDiffAt index
      (fun patch => inside time member (finProdFinEquiv (index, patch)))).1
  have derivativeContinuous : ContinuousOn
      (deriv (fun current => positiveHalfDiagonal family.patchMotion current index)) (Icc 0 finish) := by
    intro time member
    have continuous := ((regularity time member).fderiv_right (m := 0) (by norm_num)).continuousAt
    exact ((ContinuousLinearMap.apply ℝ ℂ (1 : ℝ)).continuous.continuousAt.comp continuous).continuousWithinAt
  have nonzero (time : ℝ) (member : time ∈ Icc 0 finish) :
      positiveHalfDiagonal family.patchMotion time index ≠ 0 := by
    intro zero
    have positive := differencePositive time member
    change 0 < ‖positiveHalfDiagonal family.patchMotion time index‖ ^ 2 -
      ‖negativeHalfDiagonal family.patchMotion time index‖ ^ 2 at positive
    rw [zero, norm_zero] at positive
    nlinarith [sq_nonneg ‖negativeHalfDiagonal family.patchMotion time index‖]
  have initialPolar : positiveHalfDiagonal family.patchMotion 0 index =
      (‖positiveHalfDiagonal family.patchMotion 0 index‖ : ℂ) *
        Complex.exp (Complex.I * (phase (index.val + 1) : ℂ)) := by
    obtain ⟨unstable, referenceLift, initial, _, evolution, _⟩ := prepared.referenceSolution
    have equality : positiveHalfDiagonal family.patchMotion 0 index =
        positiveHalfDiagonal prepared.reference 0 index := by
      change positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion 0 index = _
      simp only [positiveHalfDiagonal, prepared.nonterminal_initial_centroid index nonterminal]
    rw [equality, (evolution.reference_initial_diagonals (by norm_num : (0 : ℝ) ≤ 2)
      amplitudePositive frequencyPositive ratioPositive initial index).1]
    exact initialPositiveDiagonal_polar scales _ _ _
  obtain ⟨lift, continuous, initialValue, properties⟩ := General.exists_complex_phase_on_Icc finishNonnegative
    (fun time member => (regularity time member).differentiableAt (by norm_num) |>.hasDerivAt)
    derivativeContinuous nonzero initialPolar
  refine ⟨lift, continuous, initialValue, ?_⟩
  intro time member
  have rate : -scales.omega (index.val + 1) / referenceDilation scales family.patchMotion index time +
      referencePhaseError scales family.patchMotion index time =
      (deriv (fun current => positiveHalfDiagonal family.patchMotion current index) time /
        positiveHalfDiagonal family.patchMotion time index).im := by
    unfold referencePhaseError
    ring
  rw [rate]
  exact properties time member

end EulerNonuniqueness.Paper.CascadeMaterialPreparedPair
