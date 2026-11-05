import EulerNonuniqueness.Section4.PaperReferenceSharpDiagonal
import EulerNonuniqueness.Section4.PaperReferencePhaseRate

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem exists_uniform_paper_reference_sharp_phase :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧ ∃ constant ≥ (1 : ℝ), ∀ (scales : Scales),
      0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ bound ≥ (0 : ℝ), bound ≤ scales.amplitude → ∀ threshold ≤ radius,
      ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (motion : PatchMotion count) (evolution : FinitePatchEvolution changed motion 2),
      ∀ {phase unstable : Fin count → ℝ} (phaseLift : ℝ → Fin count → ℝ),
      ReferenceInitialDisks changed motion phase unstable threshold →
      ReferencePhaseLift motion phase phaseLift → ReferenceCoarseBounds changed motion threshold bound →
      ∀ index : Fin count, ∀ terminal ∈ Icc (0 : ℝ) 1,
        |phaseLift terminal index - (phase index - changed.omega (index.val + 1) * terminal)| ≤
        constant * terminal * (changed.strain + terminal * changed.strain ^ 2 + (changed.omega (index.val + 1))⁻¹ ^ 4) := by
  obtain ⟨diagonalRadius, diagonalPositive, diagonalSmall, diagonalConstant, diagonalOne, diagonal⟩ :=
    exists_uniform_paper_reference_sharp_diagonal
  obtain ⟨rateRadius, ratePositive, rateSmall, rateConstant, rateOne, phaseRate⟩ :=
    exists_uniform_paper_reference_phase_rate
  let radius := min diagonalRadius rateRadius
  let constant := 1 + 2 * diagonalConstant + rateConstant
  have diagonalNonnegative : 0 ≤ diagonalConstant := zero_le_one.trans diagonalOne
  have rateNonnegative : 0 ≤ rateConstant := zero_le_one.trans rateOne
  have radiusSmall : radius ≤ 1 / 8 := (min_le_left _ _).trans diagonalSmall
  refine ⟨radius, lt_min diagonalPositive ratePositive, radiusSmall, constant, by dsimp only [constant]; linarith only [diagonalOne, rateOne], ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold thresholdBound
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans radiusSmall
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    diagonal scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold (thresholdBound.trans (min_le_left _ _)),
    phaseRate scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold (thresholdBound.trans (min_le_right _ _)),
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative,
    scales.eventually_reference_coarse_boundary_label_gaps amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative]
    with frequency frequencyBound diagonal phaseRate mechanical labelGaps
  dsimp only
  intro count motion evolution phase unstable phaseLift initial givenLift coarse index terminal terminalInside
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith only [ratioBound]
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have terminalNonnegative := terminalInside.1
  have timeRange : Icc (0 : ℝ) terminal ⊆ Icc (0 : ℝ) 2 := Icc_subset_Icc le_rfl (terminalInside.2.trans (by norm_num))
  have info (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (source : Fin count) := mechanical motion evolution coarse time member source
  have globalControl (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (source : Fin count) (patch : Fin 4) :
      ∃ error ≤ (1 : ℝ), BoundaryCloseToCircle changed motion time source patch error :=
    ⟨bound * (changed.omega (source.val + 1))⁻¹ ^ 2,
      (info time member source).2.2.2.2.2.2.2.2.1.trans (by norm_num),
      (info time member source).2.2.2.2.2.2.2.2.2 patch⟩
  have separated (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (source other : Fin count)
      (patch otherPatch : Fin 4) (different : (other, otherPatch) ≠ (source, patch)) :=
    labelGaps motion coarse time member source other patch otherPatch different.symm
  have radiusPositive (source : Fin count) := changed.radius_pos amplitudePositive frequencyPositive ratioPositive (source.val + 1)
  have differenceLower (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (source : Fin count) := (info time member source).2.1
  have phaseWithin := evolution.referencePhaseLift_hasDerivWithinAt_of_boundary_gaps amplitudePositive frequencyPositive ratioPositive
    radiusPositive globalControl separated initial differenceLower givenLift
  have kinematics := evolution.reference_dilation_kinematics_of_boundary_gaps (by norm_num) amplitudePositive frequencyPositive ratioPositive
    radiusPositive globalControl separated index
  let phaseDerivative := fun time => -changed.omega (index.val + 1) / referenceDilation changed motion index time + referencePhaseError changed motion index time
  have equation (time : ℝ) (member : time ∈ Ioo 0 terminal) : HasDerivAt (fun current => phaseLift current index) (phaseDerivative time) time := by
    have inside : time ∈ Ioo (0 : ℝ) 2 := ⟨member.1, member.2.trans_le (terminalInside.2.trans (by norm_num))⟩
    have actual := (phaseWithin index time ⟨inside.1.le, inside.2.le⟩).hasDerivAt (Icc_mem_nhds inside.1 inside.2)
    rw [(kinematics.2 time inside).2] at actual
    convert actual using 1
    dsimp only [phaseDerivative, referencePhaseError]
    ring
  let budget := changed.strain + terminal * changed.strain ^ 2 + (changed.omega (index.val + 1))⁻¹ ^ 4
  have budgetNonnegative : 0 ≤ budget := by dsimp only [budget]; positivity
  have derivativeBound (time : ℝ) (member : time ∈ Ioo 0 terminal) : ‖phaseDerivative time - (-changed.omega (index.val + 1))‖ ≤ constant * budget := by
    have inside : time ∈ Ioo (0 : ℝ) 1 := ⟨member.1, member.2.trans_le terminalInside.2⟩
    have data := info time (timeRange ⟨member.1.le, member.2.le⟩) index
    have dilationLower : 1 / 2 ≤ referenceDilation changed motion index time := by
      exact (le_div_iff₀ (sq_pos_of_pos lengthPositive)).mpr (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using data.2.1)
    have dilationPositive : 0 < referenceDilation changed motion index time := lt_of_lt_of_le (by norm_num) dilationLower
    have inverseIdentity : 1 - (referenceDilation changed motion index time)⁻¹ =
        (referenceDilation changed motion index time - 1) / referenceDilation changed motion index time := by field_simp [dilationPositive.ne'] <;> ring <;> simp
    have inverseBound : |1 - (referenceDilation changed motion index time)⁻¹| ≤ 2 * |referenceDilation changed motion index time - 1| := by
      rw [inverseIdentity, abs_div, abs_of_pos dilationPositive]
      apply (div_le_iff₀ dilationPositive).mpr
      nlinarith only [dilationLower, abs_nonneg (referenceDilation changed motion index time - 1)]
    have diagonalBound := diagonal motion evolution phaseLift initial givenLift coarse index time ⟨inside.1.le, inside.2.le⟩
    have enlarged : |referenceDilation changed motion index time - 1| ≤
        diagonalConstant * ((changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) + (changed.omega (index.val + 1))⁻¹ ^ 5) := by
      apply diagonalBound.trans
      gcongr
      exact member.2.le
    have phaseBound := phaseRate motion evolution initial coarse time inside index
    have phaseEnlarged : |referencePhaseError changed motion index time| ≤ rateConstant * budget := by
      apply phaseBound.trans
      dsimp only [budget]
      apply mul_le_mul_of_nonneg_left _ rateNonnegative
      have extra := mul_nonneg terminalNonnegative (sq_nonneg changed.strain)
      linarith only [extra]
    have triangle : |phaseDerivative time - (-changed.omega (index.val + 1))| ≤
        |referencePhaseError changed motion index time| + changed.omega (index.val + 1) * |1 - (referenceDilation changed motion index time)⁻¹| := by
      have identity : phaseDerivative time - (-changed.omega (index.val + 1)) = referencePhaseError changed motion index time +
          changed.omega (index.val + 1) * (1 - (referenceDilation changed motion index time)⁻¹) := by dsimp only [phaseDerivative]; ring
      rw [identity]
      exact (abs_add _ _).trans_eq (by rw [abs_mul, abs_of_pos omegaPositive])
    have actual := triangle.trans (add_le_add phaseEnlarged (mul_le_mul_of_nonneg_left
      (inverseBound.trans (mul_le_mul_of_nonneg_left enlarged (by norm_num))) omegaPositive.le))
    have scalar : changed.omega (index.val + 1) * (2 * (diagonalConstant *
        ((changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) + (changed.omega (index.val + 1))⁻¹ ^ 5))) =
        2 * diagonalConstant * budget := by dsimp only [budget]; field_simp [omegaPositive.ne'] <;> ring <;> simp
    rw [scalar] at actual
    simpa only [Real.norm_eq_abs] using actual.trans (by
      have coefficient : rateConstant + 2 * diagonalConstant ≤ constant := by dsimp only [constant]; linarith only []
      simpa only [add_mul] using mul_le_mul_of_nonneg_right coefficient budgetNonnegative)
  have integrated := norm_sub_integral_le_of_interior_derivative_error terminalInside.1
    (mul_nonneg (show 0 ≤ constant by dsimp only [constant]; positivity) budgetNonnegative)
    ((givenLift index).1.mono timeRange) equation continuousOn_const derivativeBound
  rw [(givenLift index).2.1] at integrated
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, Real.norm_eq_abs] at integrated
  change |phaseLift terminal index - (phase index - changed.omega (index.val + 1) * terminal)| ≤ constant * terminal * budget
  have identity : phaseLift terminal index - (phase index - changed.omega (index.val + 1) * terminal) =
      phaseLift terminal index - phase index - terminal * (-changed.omega (index.val + 1)) := by ring
  rw [identity]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using integrated

end EulerNonuniqueness.Paper
