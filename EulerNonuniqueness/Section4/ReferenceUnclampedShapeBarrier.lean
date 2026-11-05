import EulerNonuniqueness.Section4.ReferenceStableShapeBarrier
import EulerNonuniqueness.Section4.ReferencePointRegularizedDerivative
import EulerNonuniqueness.Section4.RegularizedShapeBranch

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_unclamped_reference_shape_barrier :
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
      (∀ time ∈ Icc 0 horizon, ∀ index,
        |(regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
          (positiveHalfDiagonal family.patchMotion time index) (negativeHalfDiagonal family.patchMotion time index)).1| ≤ radius) →
      (∀ index : Fin count, referenceShapeForcingBudget scales (index.val + 1) internal memory bound ≤
        scales.omega (index.val + 1) * radius / 16) →
      ∀ time ∈ Icc 0 horizon, ∀ index : Fin count,
        0 < (negativeHalfDiagonal family.patchMotion time index / positiveHalfDiagonal family.patchMotion time index).im ∧
        regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
          (positiveHalfDiagonal family.patchMotion time index) (negativeHalfDiagonal family.patchMotion time index) =
            (unstableShape family.patchMotion time index, stableShape family.patchMotion time index) ∧
        |unstableShape family.patchMotion time index| ≤ radius ∧
        |stableShape family.patchMotion time index| < radius := by
  obtain ⟨internal, internalNonnegative, momentRadius, momentPositive, maximumRadius, maximumPositive, maximumSmall, faces⟩ :=
    exists_uniform_computed_reference_faces_all_smaller
  refine ⟨internal, internalNonnegative, momentRadius, momentPositive, maximumRadius, maximumPositive, maximumSmall, ?_⟩
  intro radius radiusPositive radiusBound count family scales horizon memory bound threshold evolution horizonNonnegative
    amplitudePositive frequencyBound ratioBound alphaPositive memoryNonnegative boundNonnegative hessianBound phase unstable initial
    thresholdSmall initialBound geometry inside material deformation control nonnegative small deformationBound lengthBound differenceLower
    differenceUpper momentBound momentSmall regularizedBound forcingSmall
  let coordinates : ℝ → Fin count → ℝ × ℝ := fun time index =>
    regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
      (positiveHalfDiagonal family.patchMotion time index) (negativeHalfDiagonal family.patchMotion time index)
  let curve : ℝ → Fin count → ℝ := fun time index => (coordinates time index).2
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have denominatorLower (time : ℝ) (member : time ∈ Icc 0 horizon) (index : Fin count) :
      scales.length (index.val + 1) ^ 2 / 2 ≤ ‖positiveHalfDiagonal family.patchMotion time index‖ ^ 2 := by
    have lower := differenceLower time member index
    dsimp only [diagonalDifference] at lower
    nlinarith [sq_nonneg ‖negativeHalfDiagonal family.patchMotion time index‖]
  have positiveNonzero (time : ℝ) (member : time ∈ Icc 0 horizon) (index : Fin count) :
      positiveHalfDiagonal family.patchMotion time index ≠ 0 := by
    intro zero
    have lower := denominatorLower time member index
    rw [zero, norm_zero] at lower
    nlinarith [sq_pos_of_pos (scales.length_pos (index.val + 1))]
  have initialPaper (index : Fin count) := evolution.reference_initial_paper_shape horizonNonnegative amplitudePositive frequencyPositive
    ratioPositive initial thresholdSmall index
  have initialCoordinates (index : Fin count) : coordinates 0 index = (unstable index, 0) := by
    have paperSmall : |unstableShape family.patchMotion 0 index| + |stableShape family.patchMotion 0 index| ≤ 1 / 4 := by
      have positiveIdentity : unstableShape family.patchMotion 0 index = unstable index := congrArg Prod.fst (initialPaper index).2
      have negativeIdentity : stableShape family.patchMotion 0 index = 0 := congrArg Prod.snd (initialPaper index).2
      rw [positiveIdentity, negativeIdentity, abs_zero, add_zero]
      exact (initialBound index).trans ((radiusBound.trans maximumSmall).trans (by norm_num))
    have chartIdentity := pointShapeChart_eq_paper_shape_of_upper family.patchMotion 0 index (initialPaper index).1
    have coherentSmall : |(pointShapeChart (positiveHalfDiagonal family.patchMotion 0 index)
        (negativeHalfDiagonal family.patchMotion 0 index)).1| +
        |(pointShapeChart (positiveHalfDiagonal family.patchMotion 0 index)
        (negativeHalfDiagonal family.patchMotion 0 index)).2| ≤ 1 / 4 := by simpa only [chartIdentity] using paperSmall
    have imaginaryGap := pointShapeChart_reference_imaginary_gap _ _ coherentSmall (initialPaper index).1
    exact (regularizedShapeCoordinates_eq_paper family.patchMotion 0 index
      (denominatorLower 0 ⟨le_rfl, horizonNonnegative⟩ index) (by linarith)).trans (initialPaper index).2
  have curveContinuous : ContinuousOn curve (Icc 0 horizon) := by
    apply continuousOn_pi.mpr
    intro index time member
    obtain ⟨positiveSmooth, negativeSmooth⟩ := family.halfDiagonals_contDiffAt index (fun patch => inside time member _)
    have lengthPositive := scales.length_pos (index.val + 1)
    have floorPositive : 0 < scales.length (index.val + 1) ^ 2 / 2 := by positivity
    exact ((regularizedShapeCoordinates_continuous floorPositive (by norm_num)).continuousAt.comp
      (positiveSmooth.continuousAt.prodMk negativeSmooth.continuousAt)).snd.continuousWithinAt
  have initialCurve : curve 0 = 0 := by funext index; exact congrArg Prod.snd (initialCoordinates index)
  have initialNorm : ‖curve 0‖ < radius := by rw [initialCurve, norm_zero]; exact radiusPositive
  have prefixFacts (terminal : ℝ) (terminalInside : terminal ∈ Icc 0 horizon)
      (prefixBound : ∀ current ∈ Icc 0 terminal, ‖curve current‖ ≤ radius) :
      ∀ time ∈ Icc 0 terminal, ∀ index : Fin count,
        0 < (negativeHalfDiagonal family.patchMotion time index / positiveHalfDiagonal family.patchMotion time index).im ∧
        coordinates time index = (unstableShape family.patchMotion time index, stableShape family.patchMotion time index) := by
    have subset : Icc (0 : ℝ) terminal ⊆ Icc 0 horizon := Icc_subset_Icc le_rfl terminalInside.2
    have coordinateSmall (time : ℝ) (member : time ∈ Icc 0 terminal) (index : Fin count) :
        |(coordinates time index).1| + |(coordinates time index).2| ≤ 1 / 4 := by
      have stableBound : |(coordinates time index).2| ≤ radius :=
        (show |curve time index| ≤ ‖curve time‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (curve time) index).trans
          (prefixBound time member)
      linarith [regularizedBound time (subset member) index, radiusBound.trans maximumSmall]
    have upperBranch (index : Fin count) : ∀ time ∈ Icc 0 terminal,
        0 < (negativeHalfDiagonal family.patchMotion time index / positiveHalfDiagonal family.patchMotion time index).im := by
      have positiveContinuous : ContinuousOn (fun time => positiveHalfDiagonal family.patchMotion time index) (Icc 0 terminal) := by
        intro time member
        exact (family.halfDiagonals_contDiffAt index (fun patch => inside time (subset member) _)).1.continuousAt.continuousWithinAt
      have negativeContinuous : ContinuousOn (fun time => negativeHalfDiagonal family.patchMotion time index) (Icc 0 terminal) := by
        intro time member
        exact (family.halfDiagonals_contDiffAt index (fun patch => inside time (subset member) _)).2.continuousAt.continuousWithinAt
      exact upperHalfPlane_of_initial_and_square_left
        (negativeContinuous.div positiveContinuous (fun time member => positiveNonzero time (subset member) index))
        (initialPaper index).1 (fun time member => regularizedShapeCoordinates_square_left
          (denominatorLower time (subset member) index) (coordinateSmall time member index))
    intro time member index
    exact ⟨upperBranch index time member, regularizedShapeCoordinates_eq_paper_of_small_upper family.patchMotion time index
      (denominatorLower time (subset member) index) (coordinateSmall time member index) (upperBranch index time member)⟩
  have confined := strictly_confined_coordinates_of_inward_derivativeWithin radiusPositive curveContinuous initialNorm (by
    intro time timeInside prefixBound index
    have closed : time ∈ Icc 0 horizon := ⟨timeInside.1.le, timeInside.2⟩
    have terminalInside : time ∈ Icc 0 time := ⟨timeInside.1.le, le_rfl⟩
    obtain ⟨upper, agreement⟩ := prefixFacts time closed prefixBound time terminalInside index
    have stableBound : |stableShape family.patchMotion time index| ≤ radius := by
      have bound : |curve time index| ≤ radius :=
        (show |curve time index| ≤ ‖curve time‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (curve time) index).trans
          (prefixBound time terminalInside)
      simpa only [curve, agreement] using bound
    have unstableBound : |unstableShape family.patchMotion time index| ≤ radius := by
      have coordinateBound : |(coordinates time index).1| ≤ radius := regularizedBound time closed index
      simpa only [agreement] using coordinateBound
    have chartSmall : |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤ 1 / 4 := by
      linarith [radiusBound.trans maximumSmall]
    have derivative := family.centroid_regularized_shape_hasDerivAt_of_point_safety evolution closed index
      (fun patch => inside time closed _) (fun patch => material time closed _) (differenceLower time closed index) upper chartSmall
    have stableDerivative := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt time derivative
    simp only [ContinuousLinearMap.coe_snd', Function.comp_def] at stableDerivative
    have computed := faces radius radiusPositive radiusBound evolution closed amplitudePositive frequencyBound ratioBound alphaPositive
      index (geometry time closed index) (control time closed index) (nonnegative time closed index) (small time closed index)
      memoryNonnegative boundNonnegative (deformationBound time closed index) (lengthBound index) hessianBound
      (differenceLower time closed index) (differenceUpper time closed index) (momentBound time closed index) (momentSmall index)
      upper unstableBound stableBound (forcingSmall index)
    have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
    have speedPositive : 0 < scales.omega (index.val + 1) * radius / 2 := by positivity
    refine ⟨(referencePointShapeVelocity scales family.patchMotion time index).2, stableDerivative.hasDerivWithinAt, ?_, ?_⟩
    · intro onFace
      have actualFace : stableShape family.patchMotion time index = radius := by simpa only [curve, agreement] using onFace
      exact (computed.2.2.1 actualFace).trans_lt (neg_neg_of_pos speedPositive)
    · intro onFace
      have actualFace : stableShape family.patchMotion time index = -radius := by simpa only [curve, agreement] using onFace
      exact speedPositive.trans_le (computed.2.2.2 actualFace))
  intro time member index
  have prefixBound : ∀ current ∈ Icc 0 time, ‖curve current‖ ≤ radius := by
    intro current currentInside
    exact (confined current ⟨currentInside.1, currentInside.2.trans member.2⟩).le
  obtain ⟨upper, agreement⟩ := prefixFacts time member prefixBound time ⟨member.1, le_rfl⟩ index
  refine ⟨upper, agreement, ?_, ?_⟩
  · have coordinateBound : |(coordinates time index).1| ≤ radius := regularizedBound time member index
    simpa only [agreement] using coordinateBound
  · have coordinateEstimate : |curve time index| ≤ ‖curve time‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (curve time) index
    simpa only [curve, agreement] using coordinateEstimate.trans_lt (confined time member)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
