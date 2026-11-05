import EulerNonuniqueness.Section4.PaperReferenceSharpImpulse
import EulerNonuniqueness.Section4.ReferenceDiagonalFromImpulse

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem exists_uniform_paper_reference_sharp_diagonal :
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
        |diagonalDifference motion terminal index / changed.length (index.val + 1) ^ 2 - 1| ≤
        constant * ((changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) +
          (changed.omega (index.val + 1))⁻¹ ^ 5) := by
  obtain ⟨radius, radiusPositive, radiusSmall, impulseConstant, impulseOne, impulse⟩ :=
    exists_uniform_paper_reference_sharp_impulse
  refine ⟨radius, radiusPositive, radiusSmall, impulseConstant + 1, by linarith only [impulseOne], ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold thresholdBound
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans radiusSmall
  filter_upwards [impulse scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold thresholdBound,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative,
    eventually_ge_atTop (1 + 48 * bound ^ 2 / scales.amplitude)]
    with frequency impulse mechanical frequencyBound
  dsimp only
  intro count motion evolution phase unstable phaseLift initial givenLift coarse index terminal terminalInside
  let changed : Scales := {scales with frequency := frequency}
  have coefficientNonnegative : 0 ≤ 48 * bound ^ 2 / scales.amplitude := by positivity
  have frequencyOne : 1 ≤ changed.frequency := by dsimp only [changed]; linarith only [frequencyBound, coefficientNonnegative]
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith only [ratioBound]
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaOne : 1 ≤ changed.omega (index.val + 1) := frequencyOne.trans
    (changed.omega_ge_frequency frequencyPositive (by dsimp only [changed]; linarith only [ratioBound]) _)
  have coefficientOmega : 48 * bound ^ 2 / changed.amplitude ≤ changed.omega (index.val + 1) ^ 2 := by
    have omegaFrequency := changed.omega_ge_frequency frequencyPositive (by dsimp only [changed]; linarith only [ratioBound]) (index.val + 1)
    have coefficientFrequency : 48 * bound ^ 2 / changed.amplitude ≤ changed.frequency := by
      dsimp only [changed]; linarith only [frequencyBound]
    have squareBound : changed.omega (index.val + 1) ≤ changed.omega (index.val + 1) ^ 2 := by
      nlinarith only [omegaOne, sq_nonneg (changed.omega (index.val + 1) - 1)]
    exact coefficientFrequency.trans (omegaFrequency.trans squareBound)
  have data := mechanical motion evolution coarse terminal ⟨terminalInside.1, terminalInside.2.trans (by norm_num)⟩ index
  have inertia := evolution.reference_diagonal_impulse_error
    ⟨terminalInside.1, terminalInside.2.trans (by norm_num)⟩ amplitudePositive frequencyPositive ratioPositive index
    data.2.2.2.2.2.2.2.2.2 data.2.2.2.2.2.2.2.1 data.2.2.2.2.2.2.2.2.1
  have tail : 48 * (bound * (changed.omega (index.val + 1))⁻¹ ^ 2) ^ 2 /
      (changed.amplitude * changed.omega (index.val + 1) ^ 3) ≤ (changed.omega (index.val + 1))⁻¹ ^ 5 := by
    have actual : (48 * bound ^ 2 / changed.amplitude) / changed.omega (index.val + 1) ^ 7 ≤
        (changed.omega (index.val + 1))⁻¹ ^ 5 := by
      apply (div_le_iff₀ (pow_pos omegaPositive 7)).mpr
      convert coefficientOmega using 1 <;> field_simp [omegaPositive.ne'] <;> ring
    have identity : 48 * (bound * (changed.omega (index.val + 1))⁻¹ ^ 2) ^ 2 /
        (changed.amplitude * changed.omega (index.val + 1) ^ 3) =
        (48 * bound ^ 2 / changed.amplitude) / changed.omega (index.val + 1) ^ 7 := by
      field_simp [omegaPositive.ne', amplitudePositive.ne'] <;> ring <;> simp
    rw [identity]
    exact actual
  have sharp := impulse motion evolution phaseLift initial givenLift coarse index terminal terminalInside
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have terminalNonnegative := terminalInside.1
  have rateNonnegative : 0 ≤ (changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) := by positivity
  apply inertia.trans ((add_le_add sharp tail).trans ?_)
  nlinarith only [rateNonnegative]

end EulerNonuniqueness.Paper
