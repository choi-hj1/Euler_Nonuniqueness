import EulerNonuniqueness.Section4.UniformReferenceSharpImpulse
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

theorem exists_uniform_actual_reference_sharp_invariants_radius :
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
      ∀ index : Fin count, ∀ terminal ∈ Icc (0 : ℝ) 1, ∀ time ∈ Icc (0 : ℝ) terminal,
        |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| +
          |angularImpulse changed family.patchMotion time index /
            (2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2) - 1| +
          |diagonalDifference family.patchMotion time index / changed.length (index.val + 1) ^ 2 - 1| ≤
            constant * ((changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) +
              (changed.omega (index.val + 1))⁻¹ ^ 5) := by
  obtain ⟨impulseRadius, impulsePositive, impulseSmall, impulseAll⟩ :=
    exists_uniform_actual_reference_sharp_impulse_radius
  obtain ⟨tubeRadius, tubePositive, tubeSmall, tubeAll⟩ :=
    exists_uniform_actual_reference_sharp_tube_radius
  let radius := min impulseRadius tubeRadius
  refine ⟨radius, by dsimp only [radius]; positivity, (min_le_left _ _).trans impulseSmall, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive bound boundNonnegative
  obtain ⟨impulseConstant, impulseOne, impulseEstimate⟩ :=
    impulseAll scales amplitudePositive ratioBound alphaPositive bound boundNonnegative
  obtain ⟨tubeConstant, tubeOne, tubeEstimate⟩ :=
    tubeAll scales amplitudePositive ratioBound alphaPositive bound boundNonnegative
  let tailConstant := 48 * bound ^ 2 / scales.amplitude
  let constant := 1 + tubeConstant + 2 * impulseConstant + tailConstant
  have tailNonnegative : 0 ≤ tailConstant := by dsimp only [tailConstant]; positivity
  have tubeNonnegative : 0 ≤ tubeConstant := zero_le_one.trans tubeOne
  have impulseNonnegative : 0 ≤ impulseConstant := zero_le_one.trans impulseOne
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith
  refine ⟨constant, constantOne, ?_⟩
  filter_upwards [impulseEstimate, tubeEstimate, eventually_ge_atTop (1 : ℝ)]
    with frequency impulseEstimate tubeEstimate frequencyBound
  dsimp only
  intro count family densityEquation radiusEquation evolution threshold phase unstable initial thresholdSmall inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation deformation control nonnegative small deformationBound upper confined
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have actualAmplitudePositive : 0 < changed.amplitude := amplitudePositive
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have impulseConfined (time : ℝ) (member : time ∈ Icc 0 2) (index : Fin count) :=
    And.intro ((confined time member index).1.trans (min_le_left _ _)) ((confined time member index).2.trans (min_le_left _ _))
  have tubeConfined (time : ℝ) (member : time ∈ Icc 0 2) (index : Fin count) :=
    And.intro ((confined time member index).1.trans (min_le_right _ _)) ((confined time member index).2.trans (min_le_right _ _))
  have impulse := impulseEstimate family densityEquation radiusEquation evolution initial thresholdSmall inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation deformation control nonnegative small deformationBound upper impulseConfined
  have tube := tubeEstimate family densityEquation radiusEquation evolution initial thresholdSmall inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation deformation control nonnegative small deformationBound upper tubeConfined
  intro index terminal terminalInside time timeInside
  have timeOne : time ∈ Icc (0 : ℝ) 1 := ⟨timeInside.1, timeInside.2.trans terminalInside.2⟩
  have timeTwo : time ∈ Icc (0 : ℝ) 2 := ⟨timeInside.1, timeOne.2.trans (by norm_num)⟩
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaOne : 1 ≤ changed.omega (index.val + 1) :=
    frequencyBound.trans (changed.omega_ge_frequency frequencyPositive (by dsimp only [changed]; linarith) _)
  have circulationPositive := changed.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have terminalNonnegative := terminalInside.1
  have deformationNonnegative := nonnegative time timeTwo index
  let normalization := 2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2
  let rate := (changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) +
    (changed.omega (index.val + 1))⁻¹ ^ 5
  have normalizationPositive : 0 < normalization := by dsimp only [normalization]; positivity
  have rateNonnegative : 0 ≤ rate := by dsimp only [rate]; positivity
  have rateMono :
      (changed.strain + time * changed.strain ^ 2) / changed.omega (index.val + 1) + (changed.omega (index.val + 1))⁻¹ ^ 5 ≤ rate := by
    dsimp only [rate]
    gcongr
    exact timeInside.2
  have impulseBound :
      |angularImpulse changed family.patchMotion time index / normalization - 1| ≤ impulseConstant * rate := by
    rw [div_sub_one normalizationPositive.ne', abs_div, abs_of_pos normalizationPositive]
    apply (div_le_iff₀ normalizationPositive).mpr
    have raw := (impulse index time timeOne).trans (mul_le_mul_of_nonneg_left rateMono
      (mul_nonneg normalizationPositive.le impulseNonnegative))
    simpa only [normalization, mul_assoc, mul_comm, mul_left_comm] using raw
  have shapeBound :
      |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤ tubeConstant * rate := by
    apply (tube index time timeOne).trans
    apply mul_le_mul_of_nonneg_left _ tubeNonnegative
    dsimp only [rate]
    apply add_le_add_right
    apply div_le_div_of_nonneg_right _ omegaPositive.le
    exact le_add_of_nonneg_right (mul_nonneg terminalNonnegative (sq_nonneg _))
  have weakerDeformation : deformation time index ≤ bound / changed.omega (index.val + 1) := by
    apply (deformationBound time timeTwo index).trans
    apply (div_le_div_iff₀ (pow_pos omegaPositive 2) omegaPositive).mpr
    have omegaSquare : changed.omega (index.val + 1) ≤ changed.omega (index.val + 1) ^ 2 := by nlinarith only [omegaOne]
    exact mul_le_mul_of_nonneg_left omegaSquare boundNonnegative
  have tailBound :
      48 * (deformation time index) ^ 2 / (changed.amplitude * changed.omega (index.val + 1) ^ 3) ≤ tailConstant * rate := by
    calc
      _ ≤ 48 * (bound / changed.omega (index.val + 1)) ^ 2 /
          (changed.amplitude * changed.omega (index.val + 1) ^ 3) := by gcongr
      _ = tailConstant * (changed.omega (index.val + 1))⁻¹ ^ 5 := by
        dsimp only [tailConstant]
        simp only [changed]
        field_simp [omegaPositive.ne', amplitudePositive.ne']
        <;> ring <;> simp
      _ ≤ tailConstant * rate := by
        apply mul_le_mul_of_nonneg_left _ tailNonnegative
        dsimp only [rate]
        exact le_add_of_nonneg_left (by positivity)
  have diagonalBound := (evolution.reference_diagonal_impulse_error timeTwo actualAmplitudePositive frequencyPositive ratioPositive
    index (control time timeTwo index) (nonnegative time timeTwo index) (small time timeTwo index)).trans (add_le_add impulseBound tailBound)
  change _ ≤ constant * rate
  apply (add_le_add (add_le_add shapeBound impulseBound) diagonalBound).trans
  calc
    _ = (tubeConstant + 2 * impulseConstant + tailConstant) * rate := by ring
    _ ≤ constant * rate := by
      apply mul_le_mul_of_nonneg_right _ rateNonnegative
      dsimp only [constant]
      linarith only []

end EulerNonuniqueness.Paper


