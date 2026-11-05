import EulerNonuniqueness.Section4.ReferenceMaterialScaleBudget
import EulerNonuniqueness.Section4.ReferenceLocalSourceEnvelope

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.exists_uniform_reference_local_material_scale_bound :
    ∃ constant ≥ (1 : ℝ), ∀ (scales : Scales) (scaleRoot : ℝ),
      scales.amplitude = scaleRoot ^ 3 → 8 ≤ scaleRoot →
      1 ≤ scales.frequency → 2 ≤ scales.ratio → scales.strain ≤ 1 →
      ∀ index : ℕ,
      0 ≤ scales.referenceLocalExteriorWeight index ∧
      scales.referenceLocalExteriorWeight index ≤ constant * scales.omega index ∧
      0 ≤ scales.radius index / (scales.length index / 400) ∧
      scales.radius index / (scales.length index / 400) ≤ constant / (scaleRoot * scales.omega index) ∧
      0 ≤ 2 * scales.circulation index ∧
      scales.referenceLocalExteriorWeight index ^ 2 +
        (2 * scales.circulation index) * scales.referenceLocalExteriorWeight index / (scales.length index / 400) ^ 2 ≤
          constant * scales.omega index ^ 2 := by
  obtain ⟨constant, constantOne, bounds⟩ := Scales.exists_uniform_reference_material_scale_bound
  refine ⟨1024 * constant, by nlinarith, ?_⟩
  intro scales scaleRoot amplitudeIdentity rootLarge frequencyLarge ratioLarge strainSmall index
  have rootPositive : 0 < scaleRoot := by linarith
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyLarge
  have ratioPositive : 0 < scales.ratio := by linarith
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive index
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive (source + 1)).le (sq_nonneg _)
  let weight := 80000 * Real.pi * scales.omega index + 2304 * scales.strain
  have weightNonnegative : 0 ≤ weight := by dsimp [weight]; positivity
  have actual := bounds scales scaleRoot amplitudeIdentity rootLarge frequencyLarge ratioLarge strainSmall
    index weight weightNonnegative le_rfl
  have constantNonnegative : 0 ≤ constant := by linarith
  have coefficient : constant ≤ 1024 * constant := by linarith
  have materialNonnegative : 0 ≤ scales.circulation index * weight / (scales.length index / 400) ^ 2 :=
    div_nonneg (mul_nonneg (scales.circulation_pos frequencyPositive ratioPositive index).le weightNonnegative) (sq_nonneg _)
  change 0 ≤ 32 * weight ∧ 32 * weight ≤ 1024 * constant * scales.omega index ∧ _
  refine ⟨by positivity, ?_, actual.2.1, ?_, by positivity, ?_⟩
  · have scaled := mul_le_mul_of_nonneg_left actual.1 (by norm_num : (0 : ℝ) ≤ 32)
    have extra : 0 ≤ (1024 - 32) * constant * scales.omega index := by positivity
    nlinarith
  · exact actual.2.2.1.trans (div_le_div_of_nonneg_right coefficient (by positivity))
  · have inflated : (32 * weight) ^ 2 + (2 * scales.circulation index) * (32 * weight) /
        (scales.length index / 400) ^ 2 ≤
        1024 * (weight ^ 2 + scales.circulation index * weight / (scales.length index / 400) ^ 2) := by
      calc
        _ = 1024 * weight ^ 2 + 64 * (scales.circulation index * weight / (scales.length index / 400) ^ 2) := by ring
        _ ≤ 1024 * weight ^ 2 + 1024 * (scales.circulation index * weight / (scales.length index / 400) ^ 2) := by linarith
        _ = _ := by ring
    have scaled := mul_le_mul_of_nonneg_left actual.2.2.2 (by norm_num : (0 : ℝ) ≤ 1024)
    exact inflated.trans (by convert scaled using 1 <;> ring)

end EulerNonuniqueness.Paper
