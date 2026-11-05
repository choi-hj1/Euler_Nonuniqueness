import EulerNonuniqueness.Section4.ReferenceImpulseSafety
import EulerNonuniqueness.Section4.ReferenceDiagonalDeformationScale
import EulerNonuniqueness.Section3.HolderPaperBoundaryBound

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000

theorem exists_uniform_reference_diagonal_prefix_improvement :
    ∃ constant ≥ (0 : ℝ), ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales),
      (∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
      ∀ {horizon finish threshold bound : ℝ},
      ∀ (evolution : FinitePatchEvolution scales family.patchMotion horizon),
      0 < horizon → 0 ≤ finish → finish ≤ 2 → Icc 0 finish ⊆ Icc 0 horizon →
      0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {phase unstable : Fin count → ℝ},
      ReferenceInitialDisks scales family.patchMotion phase unstable threshold → threshold ≤ 1 / 2 →
      (∀ time ∈ Icc 0 finish, ∀ index,
        time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime) →
      (∀ time ∈ Icc 0 finish, ∀ index label, (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label)) →
      (∀ time ∈ Icc 0 finish, ∀ index : Fin count,
        scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index) →
      (∀ time ∈ Icc 0 finish, ∀ index : Fin count,
        diagonalDifference family.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 finish, ∀ index, |radialShape family.patchMotion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 finish, ∀ index,
        ‖centroidAsymmetry family.patchMotion time index‖ ≤ scales.length (index.val + 1) / 64) →
      (∀ time ∈ Icc 0 finish, ∀ receiver source : Fin count, receiver ≠ source →
        |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
          ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖) →
      (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
      (∀ index : Fin count, scales.radius (index.val + 1) * (1 + (1 : ℝ) / 16) ≤
        scales.length (index.val + 1) / 1000) →
      (∀ index : Fin count, scales.omega (index.val + 1) * scales.length (index.val + 1) ≤ 1) →
      ∀ (deformation : ℝ → Fin count → ℝ),
      (∀ time ∈ Icc 0 finish, ∀ index patch,
        BoundaryCloseToCircle scales family.patchMotion time index patch (deformation time index)) →
      (∀ time ∈ Icc 0 finish, ∀ index, 0 ≤ deformation time index) →
      (∀ time ∈ Icc 0 finish, ∀ index, deformation time index ≤ 1 / 16) →
      (∀ time ∈ Icc 0 finish, ∀ index,
        deformation time index ≤ bound / scales.omega (index.val + 1) ^ 2) →
      scales.strain ≤ 1 → scales.hessian ≤ 1 →
      2 * constant * (scales.strain + scales.hessian) +
        48 * bound ^ 2 / (scales.amplitude * scales.frequency ^ 7) ≤ 1 / 4 →
      ∀ time ∈ Icc 0 finish, ∀ index : Fin count,
        |diagonalDifference family.patchMotion time index / scales.length (index.val + 1) ^ 2 - 1| ≤ 1 / 4 := by
  obtain ⟨constant, constantNonnegative, impulseEstimate⟩ := exists_uniform_reference_impulse_safety_bound
  refine ⟨constant, constantNonnegative, ?_⟩
  intro count family scales densityEquation horizon finish threshold bound evolution horizonPositive finishNonnegative
    finishBound timeRange amplitudePositive frequencyBound ratioBound alphaPositive phase unstable initial thresholdSmall inside
    material differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation lengthSmall radiusSmall omegaLength
    deformation control nonnegative small deformationBound strainBound hessianBound numerical
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (scales.location_pos _).le _)
  have commonControl (time : ℝ) (member : time ∈ Icc 0 finish) (index : Fin count) (patch : Fin 4) :
      BoundaryCloseToCircle scales family.patchMotion time index patch (1 / 16) := by
    obtain ⟨relabeling, periodic, relabelingBound, errorBound⟩ := control time member index patch
    exact ⟨relabeling, periodic, relabelingBound, errorBound.mono (small time member index)⟩
  have impulse := impulseEstimate family scales densityEquation evolution horizonPositive finishNonnegative finishBound timeRange
    amplitudePositive frequencyBound ratioBound alphaPositive initial thresholdSmall inside material differenceLower differenceUpper
    radialSmall asymmetrySmall centerSeparation lengthSmall commonControl (by norm_num) (by norm_num) radiusSmall omegaLength
    strainBound hessianBound
  intro time member index
  have diagonal := evolution.reference_diagonal_impulse_error (timeRange member) amplitudePositive frequencyPositive
    ratioPositive index (control time member index) (nonnegative time member index) (small time member index)
  have impulseBound := (impulse time member index).trans
    (mul_le_mul_of_nonneg_left (member.2.trans finishBound) (by positivity : 0 ≤ constant * (scales.strain + scales.hessian)))
  have deformationCost := scales.reference_diagonal_deformation_cost_le amplitudePositive frequencyPositive
    (by linarith : 1 ≤ scales.ratio) (index.val + 1) (nonnegative time member index) (deformationBound time member index)
  exact diagonal.trans ((add_le_add impulseBound deformationCost).trans ((by
    convert numerical using 1 <;> ring) :
      constant * (scales.strain + scales.hessian) * 2 +
        48 * bound ^ 2 / (scales.amplitude * scales.frequency ^ 7) ≤ 1 / 4))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
