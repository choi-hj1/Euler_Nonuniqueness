import EulerNonuniqueness.Section5.CascadeLocalSourceEnvelope
import EulerNonuniqueness.Section4.ReferenceLocalMaterialScaleBudget

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.exists_uniform_cascade_local_material_scale_bound
    (factor : ℝ) (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∃ constant ≥ (1 : ℝ), ∀ (scales : Scales) (scaleRoot : ℝ),
      scales.amplitude = scaleRoot ^ 3 → 8 ≤ scaleRoot →
      1 ≤ scales.frequency → 2 ≤ scales.ratio → scales.strain ≤ 1 →
      ∀ index : ℕ,
      0 ≤ scales.cascadeLocalExteriorWeight factor index ∧
      scales.cascadeLocalExteriorWeight factor index ≤ constant * scales.omega index ∧
      0 ≤ scales.radius index / (factor * scales.length index / 400) ∧
      scales.radius index / (factor * scales.length index / 400) ≤ constant / (scaleRoot * scales.omega index) ∧
      0 ≤ 2 * scales.circulation index ∧
      scales.cascadeLocalExteriorWeight factor index ^ 2 +
        (2 * scales.circulation index) * scales.cascadeLocalExteriorWeight factor index /
          (factor * scales.length index / 400) ^ 2 ≤ constant * scales.omega index ^ 2 := by
  obtain ⟨constant, constantOne, bounds⟩ := Scales.exists_uniform_reference_local_material_scale_bound
  have constantNonnegative : 0 ≤ constant := by linarith
  have factorSquare : factor ^ 2 ≤ 1 := pow_le_one₀ factorPositive.le factorSmall
  have fourthSquare : factor ^ 4 ≤ factor ^ 2 := by nlinarith [sq_nonneg (factor ^ 2)]
  have fourthFactor : factor ^ 4 ≤ factor := by
    have squareFactor : factor ^ 2 ≤ factor := by nlinarith
    exact fourthSquare.trans squareFactor
  have firstCoefficient : constant / factor ^ 2 ≤ constant / factor ^ 4 :=
    div_le_div_of_nonneg_left constantNonnegative (pow_pos factorPositive 4) fourthSquare
  have ratioCoefficient : constant / factor ≤ constant / factor ^ 4 :=
    div_le_div_of_nonneg_left constantNonnegative (pow_pos factorPositive 4) fourthFactor
  have constantLarge : 1 ≤ constant / factor ^ 4 := by
    apply (le_div_iff₀ (pow_pos factorPositive 4)).mpr
    nlinarith
  refine ⟨constant / factor ^ 4, constantLarge, ?_⟩
  intro scales scaleRoot amplitudeIdentity rootLarge frequencyLarge ratioLarge strainSmall index
  have actual := bounds scales scaleRoot amplitudeIdentity rootLarge frequencyLarge ratioLarge strainSmall index
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyLarge
  have ratioPositive : 0 < scales.ratio := by linarith
  have rootPositive : 0 < scaleRoot := by linarith
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  have lengthPositive := scales.length_pos index
  have weightIdentity : scales.cascadeLocalExteriorWeight factor index =
      scales.referenceLocalExteriorWeight index / factor ^ 2 := rfl
  have ratioIdentity : scales.radius index / (factor * scales.length index / 400) =
      (scales.radius index / (scales.length index / 400)) / factor := by ring
  refine ⟨by rw [weightIdentity]; exact div_nonneg actual.1 (sq_nonneg factor), ?_,
    by rw [ratioIdentity]; exact div_nonneg actual.2.2.1 factorPositive.le, ?_, actual.2.2.2.2.1, ?_⟩
  · rw [weightIdentity]
    calc
      _ ≤ constant * scales.omega index / factor ^ 2 :=
        div_le_div_of_nonneg_right actual.2.1 (sq_nonneg factor)
      _ = (constant / factor ^ 2) * scales.omega index := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right firstCoefficient omegaPositive.le
  · rw [ratioIdentity]
    calc
      _ ≤ (constant / (scaleRoot * scales.omega index)) / factor :=
        div_le_div_of_nonneg_right actual.2.2.2.1 factorPositive.le
      _ = (constant / factor) / (scaleRoot * scales.omega index) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right ratioCoefficient (by positivity)
  · rw [weightIdentity]
    have identity :
        (scales.referenceLocalExteriorWeight index / factor ^ 2) ^ 2 +
          (2 * scales.circulation index) * (scales.referenceLocalExteriorWeight index / factor ^ 2) /
            (factor * scales.length index / 400) ^ 2 =
        (scales.referenceLocalExteriorWeight index ^ 2 +
          (2 * scales.circulation index) * scales.referenceLocalExteriorWeight index /
            (scales.length index / 400) ^ 2) / factor ^ 4 := by
      field_simp
      <;> ring
    rw [identity]
    have result := div_le_div_of_nonneg_right actual.2.2.2.2.2 (pow_nonneg factorPositive.le 4)
    convert result using 1 <;> ring

end EulerNonuniqueness.Paper
