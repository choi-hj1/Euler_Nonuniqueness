import EulerNonuniqueness.Section4.ReferenceStableShapeBarrier
import EulerNonuniqueness.General.ContinuousPrefixBootstrap
import EulerNonuniqueness.Section3.FinitePatchRestriction
import EulerNonuniqueness.Section6.ReferenceChartImaginaryGap

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_regularized_reference_shape_barrier :
    ∃ internal ≥ (0 : ℝ), ∃ momentRadius > (0 : ℝ), ∃ maximumRadius > (0 : ℝ), maximumRadius ≤ 1 / 8 ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ maximumRadius →
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales}
        {horizon memory bound threshold : ℝ},
      ∀ (evolution : FinitePatchEvolution scales family.patchMotion horizon),
      0 ≤ horizon → 0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      0 ≤ memory → 0 ≤ bound → scales.hessian ≤ 1 →
      ∀ {phase unstable : Fin count → ℝ},
      ReferenceInitialDisks scales family.patchMotion phase unstable threshold → threshold ≤ 1 / 2 →
      (∀ index, |unstable index| ≤ radius) →
      (∀ time ∈ Icc 0 horizon, ∀ index, ReferenceCentroidFieldGeometry scales family.patchMotion time index) →
      (∀ time ∈ Icc 0 horizon, ∀ source,
        time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
      (∀ time ∈ Icc 0 horizon, ∀ source label, (family.patch source).boundaryVelocity time label =
        biotSavart (Paper.patchVorticity scales family.patchMotion time) ((family.patch source).boundary time label)) →
      ∀ (deformation : ℝ → Fin count → ℝ),
      (∀ time ∈ Icc 0 horizon, ∀ index patch,
        BoundaryCloseToCircle scales family.patchMotion time index patch (deformation time index)) →
      (∀ time ∈ Icc 0 horizon, ∀ index, 0 ≤ deformation time index) →
      (∀ time ∈ Icc 0 horizon, ∀ index, deformation time index ≤ 1 / 16) →
      (∀ time ∈ Icc 0 horizon, ∀ index, deformation time index ≤ bound / scales.omega (index.val + 1) ^ 2) →
      (∀ index : Fin count, scales.length (index.val + 1) ≤ 1) →
      (∀ time ∈ Icc 0 horizon, ∀ index : Fin count,
        scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index) →
      (∀ time ∈ Icc 0 horizon, ∀ index : Fin count,
        diagonalDifference family.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 horizon, ∀ index : Fin count, ‖centroidAsymmetry family.patchMotion time index‖ ≤
        memory * scales.length (index.val + 1) ^ 2) →
      (∀ index : Fin count, scales.length (index.val + 1) < momentRadius / (8 * (memory + 1))) →
      (∀ time ∈ Icc 0 horizon, ∀ index, 0 < (negativeHalfDiagonal family.patchMotion time index /
        positiveHalfDiagonal family.patchMotion time index).im) →
      (∀ time ∈ Icc 0 horizon, ∀ index,
        |(regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
          (positiveHalfDiagonal family.patchMotion time index) (negativeHalfDiagonal family.patchMotion time index)).1| ≤ radius) →
      (∀ index : Fin count, referenceShapeForcingBudget scales (index.val + 1) internal memory bound ≤
        scales.omega (index.val + 1) * radius / 16) →
      ∀ time ∈ Icc 0 horizon, ∀ index : Fin count,
        |unstableShape family.patchMotion time index| ≤ radius ∧
        |stableShape family.patchMotion time index| < radius ∧
        |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| < 1 / 4 := by
  obtain ⟨internal, internalNonnegative, momentRadius, momentPositive, maximumRadius, maximumPositive, maximumSmall, barrier⟩ :=
    exists_uniform_actual_reference_stable_barrier
  refine ⟨internal, internalNonnegative, momentRadius, momentPositive, maximumRadius, maximumPositive, maximumSmall, ?_⟩
  intro radius radiusPositive radiusBound count family scales horizon memory bound threshold evolution horizonNonnegative
    amplitudePositive frequencyBound ratioBound alphaPositive memoryNonnegative boundNonnegative hessianBound phase unstable initial
    thresholdSmall initialBound geometry inside material deformation control nonnegative small deformationBound lengthBound differenceLower
    differenceUpper momentBound momentSmall upper regularizedBound forcingSmall
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have positiveNonzero (time : ℝ) (member : time ∈ Icc 0 horizon) (index : Fin count) :
      positiveHalfDiagonal family.patchMotion time index ≠ 0 := by
    intro zero
    have lower := differenceLower time member index
    dsimp only [diagonalDifference] at lower
    rw [zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub] at lower
    nlinarith [sq_pos_of_pos (scales.length_pos (index.val + 1)), sq_nonneg ‖negativeHalfDiagonal family.patchMotion time index‖]
  let curve : ℝ → Fin count → ℝ := fun time index =>
    |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index|
  have curveContinuous : ContinuousOn curve (Icc 0 horizon) := by
    apply continuousOn_pi.mpr
    intro index time member
    have regularity := family.centroid_paper_shape_contDiffAt_of_upper index (fun patch => inside time member _)
      (positiveNonzero time member index) (upper time member index)
    exact (regularity.continuousAt.fst.abs.add regularity.continuousAt.snd.abs).continuousWithinAt
  have initialNorm : ‖curve 0‖ < 1 / 4 := by
    have initialSmall : ‖curve 0‖ ≤ radius := by
      apply pi_norm_le_iff_of_nonneg radiusPositive.le |>.mpr
      intro index
      have identity := (evolution.reference_initial_paper_shape horizonNonnegative amplitudePositive frequencyPositive ratioPositive
        initial thresholdSmall index).2
      have positiveIdentity : unstableShape family.patchMotion 0 index = unstable index := congrArg Prod.fst identity
      have negativeIdentity : stableShape family.patchMotion 0 index = 0 := congrArg Prod.snd identity
      simpa only [curve, Real.norm_eq_abs, positiveIdentity, negativeIdentity, abs_zero, add_zero, abs_abs] using initialBound index
    exact initialSmall.trans_lt (lt_of_le_of_lt (radiusBound.trans maximumSmall) (by norm_num))
  have agreement (time : ℝ) (member : time ∈ Icc 0 horizon) (index : Fin count)
      (chartSmall : |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤ 1 / 4) :
      regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal family.patchMotion time index) (negativeHalfDiagonal family.patchMotion time index) =
          (unstableShape family.patchMotion time index, stableShape family.patchMotion time index) := by
    have chartIdentity := pointShapeChart_eq_paper_shape_of_upper family.patchMotion time index (upper time member index)
    have coherentSmall : |(pointShapeChart (positiveHalfDiagonal family.patchMotion time index)
        (negativeHalfDiagonal family.patchMotion time index)).1| +
        |(pointShapeChart (positiveHalfDiagonal family.patchMotion time index)
        (negativeHalfDiagonal family.patchMotion time index)).2| ≤ 1 / 4 := by simpa only [chartIdentity] using chartSmall
    have imaginaryGap := pointShapeChart_reference_imaginary_gap _ _ coherentSmall (upper time member index)
    have denominatorLower : scales.length (index.val + 1) ^ 2 / 2 ≤ ‖positiveHalfDiagonal family.patchMotion time index‖ ^ 2 := by
      have lower := differenceLower time member index
      dsimp only [diagonalDifference] at lower
      nlinarith [sq_nonneg ‖negativeHalfDiagonal family.patchMotion time index‖]
    exact regularizedShapeCoordinates_eq_paper family.patchMotion time index denominatorLower (by linarith)
  have sharp : ∀ terminal ∈ Icc 0 horizon,
      (∀ current ∈ Icc 0 terminal, ‖curve current‖ ≤ 1 / 4) →
      ∀ time ∈ Icc 0 terminal, ∀ index, |unstableShape family.patchMotion time index| ≤ radius ∧
        |stableShape family.patchMotion time index| < radius := by
    intro terminal terminalInside prefixBound
    have subset : Icc (0 : ℝ) terminal ⊆ Icc 0 horizon := Icc_subset_Icc le_rfl terminalInside.2
    have unstableControl (time : ℝ) (member : time ∈ Icc 0 terminal) (index : Fin count) :
        |unstableShape family.patchMotion time index| ≤ radius := by
      have component : |curve time index| ≤ ‖curve time‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (curve time) index
      have chartSmall : |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤ 1 / 4 :=
        (le_abs_self (curve time index)).trans (component.trans (prefixBound time member))
      simpa only [agreement time (subset member) index chartSmall] using regularizedBound time (subset member) index
    have stableControl := barrier radius radiusPositive radiusBound family (evolution.mono terminalInside.2) terminalInside.1
      amplitudePositive frequencyBound ratioBound alphaPositive memoryNonnegative boundNonnegative hessianBound initial thresholdSmall
      (fun time member => geometry time (subset member)) (fun time member => inside time (subset member))
      (fun time member => material time (subset member)) deformation
      (fun time member => control time (subset member)) (fun time member => nonnegative time (subset member))
      (fun time member => small time (subset member)) (fun time member => deformationBound time (subset member)) lengthBound
      (fun time member => differenceLower time (subset member)) (fun time member => differenceUpper time (subset member))
      (fun time member => momentBound time (subset member)) momentSmall (fun time member => upper time (subset member))
      unstableControl forcingSmall
    intro time member index
    exact ⟨unstableControl time member index, stableControl time member index⟩
  have confined := norm_strictly_confined_of_prefix_improvement curveContinuous initialNorm (by
    intro terminal terminalInside prefixBound
    apply pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1 / 4) |>.mpr
    intro index
    obtain ⟨unstableControl, stableControl⟩ := sharp terminal terminalInside prefixBound terminal ⟨terminalInside.1, le_rfl⟩ index
    have nonnegativeValue : 0 ≤ curve terminal index := add_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg nonnegativeValue]
    dsimp only [curve]
    linarith [radiusBound.trans maximumSmall])
  intro time member index
  have prefixBound : ∀ current ∈ Icc 0 time, ‖curve current‖ ≤ 1 / 4 := by
    intro current currentInside
    exact (confined current ⟨currentInside.1, currentInside.2.trans member.2⟩).le
  obtain ⟨unstableControl, stableControl⟩ := sharp time member prefixBound time ⟨member.1, le_rfl⟩ index
  refine ⟨unstableControl, stableControl, ?_⟩
  linarith [radiusBound.trans maximumSmall]

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
