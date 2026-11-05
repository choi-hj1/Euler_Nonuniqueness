import EulerNonuniqueness.Section4.PaperReferenceSharpPhase

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem exists_uniform_paper_reference_sharp_bounds :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧ ∃ constant ≥ (1 : ℝ), ∀ (scales : Scales),
      0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ bound ≥ (0 : ℝ), bound ≤ scales.amplitude → ∀ threshold ≤ radius,
      ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (motion : PatchMotion count) (evolution : FinitePatchEvolution changed motion 2),
      ∀ {phase unstable : Fin count → ℝ} (phaseLift : ℝ → Fin count → ℝ),
      ReferenceInitialDisks changed motion phase unstable threshold →
      ReferencePhaseLift motion phase phaseLift → ReferenceCoarseBounds changed motion threshold bound →
      ∀ terminal, 0 < terminal → terminal ≤ 1 → ∀ time ∈ Icc 0 terminal, ∀ index,
        |unstableShape motion time index| + |stableShape motion time index| +
          |angularImpulse changed motion time index /
            (2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2) - 1| +
          |diagonalDifference motion time index / changed.length (index.val + 1) ^ 2 - 1| ≤
          constant * ((changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) +
            (changed.omega (index.val + 1))⁻¹ ^ 5) ∧
        |phaseLift time index - phase index + changed.omega (index.val + 1) * time| ≤
          constant * terminal * (changed.strain + terminal * changed.strain ^ 2 + (changed.omega (index.val + 1))⁻¹ ^ 4) := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, shapeConstant, shapeOne, shape⟩ := exists_uniform_paper_reference_sharp_shape
  obtain ⟨impulseRadius, impulsePositive, impulseSmall, impulseConstant, impulseOne, impulse⟩ := exists_uniform_paper_reference_sharp_impulse
  obtain ⟨diagonalRadius, diagonalPositive, diagonalSmall, diagonalConstant, diagonalOne, diagonal⟩ := exists_uniform_paper_reference_sharp_diagonal
  obtain ⟨phaseRadius, phasePositive, phaseSmall, phaseConstant, phaseOne, phaseEstimate⟩ := exists_uniform_paper_reference_sharp_phase
  let radius := min shapeRadius (min impulseRadius (min diagonalRadius phaseRadius))
  let constant := 1 + shapeConstant + impulseConstant + diagonalConstant + phaseConstant
  have shapeNonnegative : 0 ≤ shapeConstant := zero_le_one.trans shapeOne
  have impulseNonnegative : 0 ≤ impulseConstant := zero_le_one.trans impulseOne
  have diagonalNonnegative : 0 ≤ diagonalConstant := zero_le_one.trans diagonalOne
  have phaseNonnegative : 0 ≤ phaseConstant := zero_le_one.trans phaseOne
  have shapeRadiusBound : radius ≤ shapeRadius := min_le_left _ _
  have impulseRadiusBound : radius ≤ impulseRadius := (min_le_right _ _).trans (min_le_left _ _)
  have diagonalRadiusBound : radius ≤ diagonalRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have phaseRadiusBound : radius ≤ phaseRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨radius, by dsimp only [radius]; positivity, shapeRadiusBound.trans shapeSmall, constant, ?_, ?_⟩
  · dsimp only [constant]; linarith only [shapeNonnegative, impulseNonnegative, diagonalNonnegative, phaseNonnegative]
  intro scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold thresholdBound
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    shape scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold (thresholdBound.trans shapeRadiusBound),
    impulse scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold (thresholdBound.trans impulseRadiusBound),
    diagonal scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold (thresholdBound.trans diagonalRadiusBound),
    phaseEstimate scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold (thresholdBound.trans phaseRadiusBound)]
    with frequency frequencyBound shape impulse diagonal phaseEstimate
  dsimp only
  intro count motion evolution phase unstable phaseLift initial givenLift coarse terminal terminalPositive terminalBound time timeInside index
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith only [ratioBound]
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have timeNonnegative := timeInside.1
  have terminalNonnegative := terminalPositive.le
  have timeOne : time ∈ Icc (0 : ℝ) 1 := ⟨timeInside.1, timeInside.2.trans terminalBound⟩
  let rate := (changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) + (changed.omega (index.val + 1))⁻¹ ^ 5
  have rateNonnegative : 0 ≤ rate := by dsimp only [rate]; positivity
  have shapeBound : |unstableShape motion time index| + |stableShape motion time index| ≤ shapeConstant * rate := by
    apply (shape motion evolution initial coarse time timeOne index).1.trans
    dsimp only [rate]
    apply mul_le_mul_of_nonneg_left _ shapeNonnegative
    apply add_le_add_right _ _
    apply div_le_div_of_nonneg_right _ omegaPositive.le
    have extra := mul_nonneg terminalNonnegative (sq_nonneg changed.strain)
    linarith only [extra]
  have impulseBound : |angularImpulse changed motion time index /
      (2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2) - 1| ≤ impulseConstant * rate := by
    apply (impulse motion evolution phaseLift initial givenLift coarse index time timeOne).trans
    dsimp only [rate]
    gcongr <;> exact timeInside.2
  have diagonalBound : |diagonalDifference motion time index / changed.length (index.val + 1) ^ 2 - 1| ≤ diagonalConstant * rate := by
    apply (diagonal motion evolution phaseLift initial givenLift coarse index time timeOne).trans
    dsimp only [rate]
    gcongr <;> exact timeInside.2
  constructor
  · have actual := add_le_add (add_le_add shapeBound impulseBound) diagonalBound
    apply actual.trans
    have coefficient : shapeConstant + impulseConstant + diagonalConstant ≤ constant := by dsimp only [constant]; linarith only [phaseNonnegative]
    simpa only [add_mul] using mul_le_mul_of_nonneg_right coefficient rateNonnegative
  · have actual := phaseEstimate motion evolution phaseLift initial givenLift coarse index time timeOne
    have identity : phaseLift time index - (phase index - changed.omega (index.val + 1) * time) =
        phaseLift time index - phase index + changed.omega (index.val + 1) * time := by ring
    rw [identity] at actual
    apply actual.trans
    have coefficient : phaseConstant ≤ constant := by dsimp only [constant]; linarith only [shapeNonnegative, impulseNonnegative, diagonalNonnegative]
    gcongr <;> first | exact coefficient | exact timeInside.2 | positivity

end EulerNonuniqueness.Paper
