import EulerNonuniqueness.Section4.PaperReferenceSharpShape

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem exists_uniform_paper_reference_phase_rate :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧ ∃ constant ≥ (1 : ℝ), ∀ (scales : Scales),
      0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ bound ≥ (0 : ℝ), bound ≤ scales.amplitude → ∀ threshold ≤ radius,
      ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (motion : PatchMotion count) (evolution : FinitePatchEvolution changed motion 2),
      ∀ {phase unstable : Fin count → ℝ}, ReferenceInitialDisks changed motion phase unstable threshold →
      ReferenceCoarseBounds changed motion threshold bound →
      ∀ time ∈ Ioo (0 : ℝ) 1, ∀ index : Fin count,
        |referencePhaseError changed motion index time| ≤
          constant * (changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4) := by
  obtain ⟨radius, radiusPositive, radiusSmall, tubeConstant, tubeOne, tube⟩ :=
    exists_uniform_paper_reference_sharp_shape
  obtain ⟨internal, internalNonnegative, momentRadius, momentPositive, phaseConstant, phaseNonnegative,
    phaseRadius, phasePositive, estimate⟩ := exists_uniform_paper_phase_dilation_estimates
  let first := (2 * internal + 4608) / Real.pi
  let second := 27648000000 + 226492416 / Real.pi
  let oddConstant := first + second
  let constant := 1 + 2 * phaseConstant * tubeConstant + oddConstant
  have firstNonnegative : 0 ≤ first := by dsimp only [first]; positivity
  have secondNonnegative : 0 ≤ second := by dsimp only [second]; positivity
  have oddNonnegative : 0 ≤ oddConstant := add_nonneg firstNonnegative secondNonnegative
  have tubeNonnegative : 0 ≤ tubeConstant := zero_le_one.trans tubeOne
  have mixedNonnegative : 0 ≤ 2 * phaseConstant * tubeConstant := by positivity
  refine ⟨radius, radiusPositive, radiusSmall, constant, ?_, ?_⟩
  · dsimp only [constant]; linarith only [oddNonnegative, mixedNonnegative]
  intro scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold thresholdBound
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans radiusSmall
  have tolerancePositive : 0 < min (1 : ℝ) (momentRadius / 16) := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    tube scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold thresholdBound,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative,
    scales.eventually_reference_coarse_boundary_label_gaps amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative,
    scales.eventually_omega_pow_length_lt (by linarith only [ratioBound] : 1 < scales.ratio) alphaPositive 0 tolerancePositive,
    scales.eventually_uniform_reference_tube_small ratioBound alphaPositive tubeNonnegative phasePositive,
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyBound sharp mechanical labelGaps tinyLengths chartSmall hessianSmall
  dsimp only
  intro count motion evolution phase unstable initial coarse time member index
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith only [ratioBound]
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have timeInside : time ∈ Icc (0 : ℝ) 2 := ⟨member.1.le, member.2.le.trans (by norm_num)⟩
  have info (current : ℝ) (inside : current ∈ Icc (0 : ℝ) 2) (source : Fin count) := mechanical motion evolution coarse current inside source
  have data := info time timeInside index
  have globalControl (current : ℝ) (inside : current ∈ Icc (0 : ℝ) 2) (source : Fin count) (patch : Fin 4) :
      ∃ error ≤ (1 : ℝ), BoundaryCloseToCircle changed motion current source patch error :=
    ⟨bound * (changed.omega (source.val + 1))⁻¹ ^ 2,
      (info current inside source).2.2.2.2.2.2.2.2.1.trans (by norm_num),
      (info current inside source).2.2.2.2.2.2.2.2.2 patch⟩
  have separated (current : ℝ) (inside : current ∈ Icc (0 : ℝ) 2) (source other : Fin count)
      (patch otherPatch : Fin 4) (different : (other, otherPatch) ≠ (source, patch)) :=
    labelGaps motion coarse current inside source other patch otherPatch different.symm
  have tiny : changed.length (index.val + 1) < min (1 : ℝ) (momentRadius / 16) := by
    simpa only [pow_zero, one_mul] using tinyLengths (index.val + 1)
  have lengthBound : changed.length (index.val + 1) ≤ 1 := (tiny.trans_le (min_le_left _ _)).le
  have momentSmall : changed.length (index.val + 1) < momentRadius / (8 * ((1 : ℝ) + 1)) := by
    simpa only [show (8 : ℝ) * (1 + 1) = 16 by norm_num] using tiny.trans_le (min_le_right _ _)
  have paperSmall : |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4 := by
    have q := data.2.2.2.2.1
    have p := data.2.2.2.2.2.1
    linarith only [q, p, thresholdSmall]
  have actual := (estimate evolution (by norm_num) amplitudePositive frequencyBound ratioBound alphaPositive
    (fun source => changed.radius_pos amplitudePositive frequencyPositive ratioPositive (source.val + 1))
    globalControl separated ⟨member.1, member.2.trans (by norm_num)⟩ index data.1
    data.2.2.2.2.2.2.2.2.2 data.2.2.2.2.2.2.2.1 data.2.2.2.2.2.2.2.2.1
    (by norm_num : (0 : ℝ) ≤ 1) boundNonnegative
    (by simp only [div_eq_mul_inv, inv_pow]; exact le_rfl) lengthBound hessianSmall.le data.2.1 data.2.2.1
    (by simpa only [one_mul] using data.2.2.2.1) momentSmall paperSmall).2
      ((sharp motion evolution initial coarse time ⟨member.1.le, member.2.le⟩ index).1.trans_lt (chartSmall (index.val + 1)))
  have oddBudget : referenceOddForcingBudget changed (index.val + 1) internal 1 bound ≤
      oddConstant * (changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4) := by
    have coefficientBound : second * bound / changed.amplitude ≤ second :=
      (div_le_iff₀ amplitudePositive).mpr (mul_le_mul_of_nonneg_left amplitudeBound secondNonnegative)
    have combined := add_le_add
      (mul_le_mul_of_nonneg_right (show first ≤ oddConstant by dsimp only [oddConstant]; linarith only [secondNonnegative]) strainNonnegative)
      (mul_le_mul_of_nonneg_right (coefficientBound.trans (show second ≤ oddConstant by dsimp only [oddConstant]; linarith only [firstNonnegative]))
        (by positivity : 0 ≤ (changed.omega (index.val + 1))⁻¹ ^ 4))
    simpa only [referenceOddForcingBudget, first, second, one_pow, mul_one, inv_pow, div_eq_mul_inv, mul_add] using combined
  have multiplied := mul_le_mul_of_nonneg_left (sharp motion evolution initial coarse time ⟨member.1.le, member.2.le⟩ index).1
    (by positivity : 0 ≤ 2 * phaseConstant * changed.omega (index.val + 1))
  have total := actual.trans (add_le_add multiplied oddBudget)
  have identity : 2 * phaseConstant * changed.omega (index.val + 1) *
      (tubeConstant * (changed.strain / changed.omega (index.val + 1) + (changed.omega (index.val + 1))⁻¹ ^ 5)) +
      oddConstant * (changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4) =
      (2 * phaseConstant * tubeConstant + oddConstant) * (changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4) := by
    field_simp [omegaPositive.ne'] <;> ring
  rw [identity] at total
  apply total.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  dsimp only [constant]; linarith only []

end EulerNonuniqueness.Paper
