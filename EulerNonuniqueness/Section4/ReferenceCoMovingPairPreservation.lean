import EulerNonuniqueness.Section4.ReferencePairwiseSafety

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

private theorem pair_norm_bounds_of_relative_error {current reference : ℂ} {gap : ℝ}
    (gapNonnegative : 0 ≤ gap) (referenceNorm : ‖reference‖ = gap)
    (estimate : ‖current - reference‖ ≤ gap / 2) : gap / 2 ≤ ‖current‖ ∧ ‖current‖ ≤ 2 * gap := by
  have upper : ‖current‖ ≤ ‖current - reference‖ + ‖reference‖ := by
    simpa only [sub_add_cancel] using norm_add_le (current - reference) reference
  have lower : ‖reference‖ ≤ ‖current - reference‖ + ‖current‖ := by
    simpa only [sub_add_cancel, norm_sub_rev] using norm_add_le (reference - current) current
  rw [referenceNorm] at upper lower
  constructor <;> linarith only [upper, lower, estimate, gapNonnegative]

theorem FiniteMovingPatchFamily.reference_pair_prefix_improvement {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon finish error tolerance threshold : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (horizonNonnegative : 0 ≤ horizon) (finishBound : finish ≤ 2)
    (timeRange : Icc 0 finish ⊆ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {phase unstable : Fin count → ℝ}
    (initial : ReferenceInitialDisks scales family.patchMotion phase unstable threshold)
    (inside : ∀ time ∈ Icc 0 finish, ∀ index,
      time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ time ∈ Icc 0 finish, ∀ index label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (differenceLower : ∀ time ∈ Icc 0 finish, ∀ index : Fin count,
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index)
    (differenceUpper : ∀ time ∈ Icc 0 finish, ∀ index : Fin count,
      diagonalDifference family.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : ∀ time ∈ Icc 0 finish, ∀ index, |radialShape family.patchMotion time index| ≤ 1 / 2)
    (asymmetrySmall : ∀ time ∈ Icc 0 finish, ∀ index,
      ‖centroidAsymmetry family.patchMotion time index‖ ≤ scales.length (index.val + 1) / 64)
    (pairPrefix : ∀ time ∈ Icc 0 finish, ∀ first second : Fin count, first ≠ second →
      ‖(quadrupoleCenter family.patchMotion time first - quadrupoleCenter family.patchMotion time second) -
          ((scales.location (first.val + 1) : ℂ) - (scales.location (second.val + 1) : ℂ))‖ ≤
        |scales.location (first.val + 1) - scales.location (second.val + 1)| / 2)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (control : ∀ time ∈ Icc 0 finish, ∀ index patch,
      BoundaryCloseToCircle scales family.patchMotion time index patch error)
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 16)
    (radiusSmall : ∀ index : Fin count,
      scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 1000)
    (toleranceNonnegative : 0 ≤ tolerance)
    (omegaLength : ∀ index : Fin count, scales.omega (index.val + 1) * scales.length (index.val + 1) ≤
      tolerance * scales.location (index.val + 1))
    (numerical : 2 * ((15120 / Real.pi) * scales.strain + 1800 * tolerance) ≤ 1 / 4) :
    ∀ time ∈ Icc 0 finish, ∀ first second : Fin count, first ≠ second →
      ‖(quadrupoleCenter family.patchMotion time first - quadrupoleCenter family.patchMotion time second) -
          ((scales.location (first.val + 1) : ℂ) - (scales.location (second.val + 1) : ℂ))‖ ≤
        |scales.location (first.val + 1) - scales.location (second.val + 1)| / 4 := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have rateNonnegative : 0 ≤ (15120 / Real.pi) * scales.strain + 1800 * tolerance := by positivity
  have pairs (time : ℝ) (member : time ∈ Icc 0 finish) (first second : Fin count) (different : first ≠ second) :=
    pair_norm_bounds_of_relative_error (abs_nonneg (scales.location (first.val + 1) - scales.location (second.val + 1)))
      (show ‖(scales.location (first.val + 1) : ℂ) - (scales.location (second.val + 1) : ℂ)‖ =
        |scales.location (first.val + 1) - scales.location (second.val + 1)| by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs])
      (pairPrefix time member first second different)
  have actual := family.reference_pair_center_change_bound scales densityEquation evolution horizonNonnegative timeRange
    amplitudePositive frequencyBound ratioBound alphaPositive initial inside material differenceLower differenceUpper radialSmall
    asymmetrySmall (fun time member first second different => (pairs time member first second different).1)
    (fun time member first second different => (pairs time member first second different).2)
    lengthSmall control errorNonnegative errorSmall radiusSmall toleranceNonnegative omegaLength
  intro time member first second different
  have timeBound : time ≤ 2 := member.2.trans finishBound
  have scaledTime := mul_le_mul_of_nonneg_left timeBound rateNonnegative
  have small : ((15120 / Real.pi) * scales.strain + 1800 * tolerance) * time ≤ 1 / 4 := by
    linarith only [scaledTime, numerical]
  calc
    _ ≤ ((15120 / Real.pi) * scales.strain + 1800 * tolerance) *
        |scales.location (first.val + 1) - scales.location (second.val + 1)| * time := actual time member first second different
    _ = (((15120 / Real.pi) * scales.strain + 1800 * tolerance) * time) *
        |scales.location (first.val + 1) - scales.location (second.val + 1)| := by ring
    _ ≤ (1 / 4) * |scales.location (first.val + 1) - scales.location (second.val + 1)| :=
      mul_le_mul_of_nonneg_right small (abs_nonneg _)
    _ = _ := by ring

end EulerNonuniqueness.Paper
