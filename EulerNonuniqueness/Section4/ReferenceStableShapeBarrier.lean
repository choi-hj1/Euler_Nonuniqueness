import EulerNonuniqueness.General.InwardBarrier
import EulerNonuniqueness.Section4.ReferenceSmallerFaceRadius
import EulerNonuniqueness.Section4.ReferencePaperShapeRegularity
import EulerNonuniqueness.Section4.ReferenceInitialShapeCoordinates

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_actual_reference_stable_barrier :
    ∃ internal ≥ (0 : ℝ), ∃ momentRadius > (0 : ℝ), ∃ maximumRadius > (0 : ℝ), maximumRadius ≤ 1 / 8 ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ maximumRadius →
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales}
        {horizon memory bound threshold : ℝ},
      ∀ (evolution : FinitePatchEvolution scales family.patchMotion horizon),
      0 ≤ horizon → 0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      0 ≤ memory → 0 ≤ bound → scales.hessian ≤ 1 →
      ∀ {phase unstable : Fin count → ℝ},
      ReferenceInitialDisks scales family.patchMotion phase unstable threshold → threshold ≤ 1 / 2 →
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
      (∀ time ∈ Icc 0 horizon, ∀ index, |unstableShape family.patchMotion time index| ≤ radius) →
      (∀ index : Fin count, referenceShapeForcingBudget scales (index.val + 1) internal memory bound ≤
        scales.omega (index.val + 1) * radius / 16) →
      ∀ time ∈ Icc 0 horizon, ∀ index : Fin count, |stableShape family.patchMotion time index| < radius := by
  obtain ⟨internal, internalNonnegative, momentRadius, momentRadiusPositive, maximumRadius, maximumPositive,
    maximumSmall, faces⟩ := exists_uniform_computed_reference_faces_all_smaller
  refine ⟨internal, internalNonnegative, momentRadius, momentRadiusPositive, maximumRadius, maximumPositive, maximumSmall, ?_⟩
  intro radius radiusPositive radiusBound count family scales horizon memory bound threshold evolution horizonNonnegative
    amplitudePositive frequencyBound ratioBound alphaPositive memoryNonnegative boundNonnegative hessianBound phase unstable initial
    thresholdSmall geometry inside material deformation control nonnegative small deformationBound lengthBound differenceLower
    differenceUpper momentBound momentSmall upper unstableBound forcingSmall
  let curve : ℝ → Fin count → ℝ := fun time index => stableShape family.patchMotion time index
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have positiveNonzero (time : ℝ) (member : time ∈ Icc 0 horizon) (index : Fin count) :
      positiveHalfDiagonal family.patchMotion time index ≠ 0 := by
    intro zero
    have lower := differenceLower time member index
    dsimp only [diagonalDifference] at lower
    rw [zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub] at lower
    nlinarith [sq_pos_of_pos (scales.length_pos (index.val + 1)), sq_nonneg ‖negativeHalfDiagonal family.patchMotion time index‖]
  have curveContinuous : ContinuousOn curve (Icc 0 horizon) := by
    apply continuousOn_pi.mpr
    intro index time member
    have regularity := family.centroid_paper_shape_contDiffAt_of_upper index (fun patch => inside time member _)
      (positiveNonzero time member index) (upper time member index)
    exact regularity.continuousAt.snd.continuousWithinAt
  have initialCurve : curve 0 = 0 := by
    funext index
    exact congrArg Prod.snd (evolution.reference_initial_paper_shape horizonNonnegative amplitudePositive frequencyPositive
      ratioPositive initial thresholdSmall index).2
  have initialNorm : ‖curve 0‖ < radius := by rw [initialCurve, norm_zero]; exact radiusPositive
  have confined := strictly_confined_coordinates_of_inward_derivativeWithin radiusPositive curveContinuous initialNorm (by
    intro time timeInside prefixBound index
    have closed : time ∈ Icc 0 horizon := ⟨timeInside.1.le, timeInside.2⟩
    have stableBound : |stableShape family.patchMotion time index| ≤ radius := by
      have coordinateEstimate : |curve time index| ≤ ‖curve time‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (curve time) index
      exact coordinateEstimate.trans (prefixBound time ⟨timeInside.1.le, le_rfl⟩)
    have shapeSmall : |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤ 1 / 4 := by
      linarith [unstableBound time closed index, radiusBound.trans maximumSmall]
    have derivative := family.centroid_paper_shape_hasDerivAt_of_upper evolution closed index
      (fun patch => inside time closed _) (fun patch => material time closed _) (upper time closed index) shapeSmall
    have stableDerivative := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt time derivative
    simp only [ContinuousLinearMap.coe_snd', Function.comp_def] at stableDerivative
    have computed := faces radius radiusPositive radiusBound evolution closed amplitudePositive frequencyBound ratioBound alphaPositive
      index (geometry time closed index) (control time closed index) (nonnegative time closed index) (small time closed index)
      memoryNonnegative boundNonnegative (deformationBound time closed index) (lengthBound index) hessianBound
      (differenceLower time closed index) (differenceUpper time closed index) (momentBound time closed index) (momentSmall index)
      (upper time closed index) (unstableBound time closed index) stableBound (forcingSmall index)
    refine ⟨(referencePointShapeVelocity scales family.patchMotion time index).2, stableDerivative.hasDerivWithinAt, ?_, ?_⟩
    · intro onFace
      have estimate := computed.2.2.1 onFace
      have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
      have speedPositive : 0 < scales.omega (index.val + 1) * radius / 2 := by positivity
      linarith
    · intro onFace
      have estimate := computed.2.2.2 onFace
      have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
      have speedPositive : 0 < scales.omega (index.val + 1) * radius / 2 := by positivity
      linarith)
  intro time member index
  have coordinateEstimate : |curve time index| ≤ ‖curve time‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (curve time) index
  exact coordinateEstimate.trans_lt (confined time member)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
