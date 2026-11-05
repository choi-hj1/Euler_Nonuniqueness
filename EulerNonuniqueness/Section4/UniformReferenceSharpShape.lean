import EulerNonuniqueness.Section4.UniformReferenceSharpInvariants
import EulerNonuniqueness.Section4.UniformReferencePhaseData
import EulerNonuniqueness.General.PhaseDilationControl
import EulerNonuniqueness.Section4.ReferenceDiagonalFromImpulse
import EulerNonuniqueness.General.WeightedPrimitiveBound
import EulerNonuniqueness.Section4.ReferenceIntegratedImpulse
import EulerNonuniqueness.Section4.ReferenceSharpInteriorTube
import EulerNonuniqueness.Section4.ReferenceNeutralPrefixSafety

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_actual_reference_sharp_shape_radius :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
      ∀ (scales : Scales), 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ (bound : ℝ), 0 ≤ bound → ∃ constant ≥ (1 : ℝ),
      ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)),
      (∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4) →
      (∀ (index : Fin count) (patch : Fin 4), (family.patch (finProdFinEquiv (index, patch))).radius = changed.radius (index.val + 1)) →
      ∀ (evolution : FinitePatchEvolution changed family.patchMotion 2), ∀ {threshold : ℝ}, ∀ {phase unstable : Fin count → ℝ},
      ReferenceInitialDisks changed family.patchMotion phase unstable threshold → threshold ≤ 1 / 2 →
      (∀ time ∈ Icc 0 2, ∀ source, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
      (∀ time ∈ Icc 0 2, ∀ source label, (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label)) →
      (∀ time ∈ Icc 0 2, ∀ index : Fin count, changed.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index) →
      (∀ time ∈ Icc 0 2, ∀ index : Fin count, diagonalDifference family.patchMotion time index ≤ 2 * changed.length (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 2, ∀ index, |radialShape family.patchMotion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 2, ∀ index, ‖centroidAsymmetry family.patchMotion time index‖ ≤ changed.length (index.val + 1) / 64) →
      (∀ time ∈ Icc 0 2, ∀ receiver source : Fin count, receiver ≠ source →
        |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 2 ≤
          ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖) →
      ∀ (deformation : ℝ → Fin count → ℝ),
      (∀ time ∈ Icc 0 2, ∀ index patch, BoundaryCloseToCircle changed family.patchMotion time index patch (deformation time index)) →
      (∀ time ∈ Icc 0 2, ∀ index, 0 ≤ deformation time index) →
      (∀ time ∈ Icc 0 2, ∀ index, deformation time index ≤ 1 / 16) →
      (∀ time ∈ Icc 0 2, ∀ index, deformation time index ≤ bound / changed.omega (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 2, ∀ index, 0 < (negativeHalfDiagonal family.patchMotion time index / positiveHalfDiagonal family.patchMotion time index).im) →
      (∀ time ∈ Icc 0 2, ∀ index, |unstableShape family.patchMotion time index| ≤ radius ∧ |stableShape family.patchMotion time index| ≤ radius) →
      ∃ phaseLift : ℝ → Fin count → ℝ, ReferencePhaseLift family.patchMotion phase phaseLift ∧
        ∀ index : Fin count, ∀ terminal ∈ Icc (0 : ℝ) 1, ∀ time ∈ Icc (0 : ℝ) terminal,
          (|unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| +
            |angularImpulse changed family.patchMotion time index /
              (2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2) - 1| +
            |diagonalDifference family.patchMotion time index / changed.length (index.val + 1) ^ 2 - 1| ≤
              constant * ((changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) +
                (changed.omega (index.val + 1))⁻¹ ^ 5)) ∧
          (|phaseLift time index - phase index + changed.omega (index.val + 1) * time| ≤
            constant * terminal * (changed.strain + terminal * changed.strain ^ 2 +
              (changed.omega (index.val + 1))⁻¹ ^ 4)) := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, shapeAll⟩ :=
    exists_uniform_actual_reference_sharp_invariants_radius
  obtain ⟨phaseRadius, phasePositive, phaseSmall, phaseAll⟩ :=
    exists_uniform_actual_reference_phase_data_radius
  let radius := min shapeRadius phaseRadius
  refine ⟨radius, by dsimp only [radius]; positivity, (min_le_left _ _).trans shapeSmall, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive bound boundNonnegative
  obtain ⟨shapeConstant, shapeOne, shapeEstimate⟩ :=
    shapeAll scales amplitudePositive ratioBound alphaPositive bound boundNonnegative
  obtain ⟨phaseConstant, phaseOne, phaseEstimate⟩ :=
    phaseAll scales amplitudePositive ratioBound alphaPositive bound boundNonnegative
  let constant := 1 + 2 * shapeConstant + phaseConstant
  have shapeNonnegative : 0 ≤ shapeConstant := zero_le_one.trans shapeOne
  have phaseNonnegative : 0 ≤ phaseConstant := zero_le_one.trans phaseOne
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith only [shapeNonnegative, phaseNonnegative]
  have shapeConstantBound : shapeConstant ≤ constant := by dsimp only [constant]; linarith only [shapeNonnegative, phaseNonnegative]
  have phaseConstantBound : 2 * shapeConstant + phaseConstant ≤ constant := by dsimp only [constant]; linarith only []
  refine ⟨constant, constantOne, ?_⟩
  filter_upwards [shapeEstimate, phaseEstimate, eventually_ge_atTop (1 : ℝ)] with frequency shapeEstimate phaseEstimate frequencyBound
  dsimp only
  intro count family densityEquation radiusEquation evolution threshold phase unstable initial thresholdSmall inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation deformation control nonnegative small deformationBound upper confined
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have shapeConfined (time : ℝ) (member : time ∈ Icc 0 2) (index : Fin count) :=
    And.intro ((confined time member index).1.trans (min_le_left _ _)) ((confined time member index).2.trans (min_le_left _ _))
  have phaseConfined (time : ℝ) (member : time ∈ Icc 0 2) (index : Fin count) :=
    And.intro ((confined time member index).1.trans (min_le_right _ _)) ((confined time member index).2.trans (min_le_right _ _))
  have shape := shapeEstimate family densityEquation radiusEquation evolution initial thresholdSmall inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation deformation control nonnegative small deformationBound upper shapeConfined
  obtain ⟨phaseLift, lift, equation, remainderBound⟩ := phaseEstimate family densityEquation radiusEquation evolution initial thresholdSmall inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation deformation control nonnegative small deformationBound upper phaseConfined
  refine ⟨phaseLift, lift, ?_⟩
  intro index terminal terminalInside time timeInside
  have timeOne : time ∈ Icc (0 : ℝ) 1 := ⟨timeInside.1, timeInside.2.trans terminalInside.2⟩
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have terminalNonnegative := terminalInside.1
  have timeNonnegative := timeInside.1
  constructor
  · apply (shape index terminal terminalInside time timeInside).trans
    apply mul_le_mul_of_nonneg_right shapeConstantBound
    positivity
  · have dilationLower (current : ℝ) (member : current ∈ Icc 0 time) :
        1 / 2 ≤ referenceDilation changed family.patchMotion index current := by
      apply (le_div_iff₀ (sq_pos_of_pos lengthPositive)).mpr
      simpa only [div_eq_mul_inv, mul_comm, one_mul] using
        differenceLower current ⟨member.1, member.2.trans (timeOne.2.trans (by norm_num))⟩ index
    have dilationBound (current : ℝ) (member : current ∈ Icc 0 time) :
        |referenceDilation changed family.patchMotion index current - 1| ≤
          shapeConstant * ((changed.strain + time * changed.strain ^ 2) / changed.omega (index.val + 1) +
            (changed.omega (index.val + 1))⁻¹ ^ 5) := by
      apply le_trans _ (shape index time timeOne current member)
      dsimp only [referenceDilation]
      nlinarith only [abs_nonneg (unstableShape family.patchMotion current index),
        abs_nonneg (stableShape family.patchMotion current index),
        abs_nonneg (angularImpulse changed family.patchMotion current index /
          (2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2) - 1)]
    have actual := EulerNonuniqueness.phase_dilation_increment_bound omegaPositive timeInside.1 strainNonnegative shapeNonnegative phaseNonnegative
      (fun current member => equation index current ⟨member.1, member.2.trans (timeOne.2.trans (by norm_num))⟩)
      dilationLower dilationBound
      (fun current member => remainderBound index current ⟨member.1, member.2.trans timeOne.2⟩)
    rw [(lift index).2.1] at actual
    apply actual.trans
    apply mul_le_mul
    · exact mul_le_mul phaseConstantBound timeInside.2 timeInside.1 (zero_le_one.trans constantOne)
    · apply add_le_add_right
      apply add_le_add_left
      exact mul_le_mul_of_nonneg_right timeInside.2 (sq_nonneg _)
    · positivity
    · positivity

end EulerNonuniqueness.Paper

