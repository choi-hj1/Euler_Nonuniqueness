import EulerNonuniqueness.Section1.UniformScaleBounds
import EulerNonuniqueness.General.QuarticGeometricRatio

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000

theorem Scales.exists_uniform_reference_material_scale_bound :
    ∃ constant ≥ (1 : ℝ), ∀ (scales : Scales) (scaleRoot : ℝ),
      scales.amplitude = scaleRoot ^ 3 → 8 ≤ scaleRoot →
      1 ≤ scales.frequency → 2 ≤ scales.ratio → scales.strain ≤ 1 →
      ∀ (index : ℕ) (weight : ℝ), 0 ≤ weight →
      weight ≤ 80000 * Real.pi * scales.omega index + 2304 * scales.strain →
      weight ≤ constant * scales.omega index ∧
      0 ≤ scales.radius index / (scales.length index / 400) ∧
      scales.radius index / (scales.length index / 400) ≤ constant / (scaleRoot * scales.omega index) ∧
      weight ^ 2 + scales.circulation index * weight / (scales.length index / 400) ^ 2 ≤
        constant * scales.omega index ^ 2 := by
  let coefficient := 80000 * Real.pi + 2304
  let constant := 1001 + coefficient + coefficient ^ 2 + 320000 * Real.pi * coefficient
  have coefficientPositive : 0 < coefficient := by dsimp only [coefficient]; positivity
  have materialNonnegative : 0 ≤ 320000 * Real.pi * coefficient := by positivity
  have constantOne : 1 ≤ constant := by dsimp only [constant]; nlinarith [sq_nonneg coefficient]
  have weightCoefficient : coefficient ≤ constant := by dsimp only [constant]; nlinarith [sq_nonneg coefficient]
  have ratioCoefficient : 1000 ≤ constant := by dsimp only [constant]; nlinarith [sq_nonneg coefficient]
  have materialCoefficient : coefficient ^ 2 + 320000 * Real.pi * coefficient ≤ constant := by
    dsimp only [constant]
    linarith
  refine ⟨constant, constantOne, ?_⟩
  intro scales scaleRoot amplitudeIdentity rootLarge frequencyLarge ratioLarge strainSmall index weight weightNonnegative weightBound
  have rootPositive : 0 < scaleRoot := by linarith
  have frequencyPositive : 0 < scales.frequency := by linarith
  have ratioPositive : 0 < scales.ratio := by linarith
  have omegaLarge : 1 ≤ scales.omega index := frequencyLarge.trans
    (scales.omega_ge_frequency frequencyPositive (by linarith) index)
  have omegaPositive : 0 < scales.omega index := by linarith
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have lengthPositive := scales.length_pos index
  have radiusPositive := scales.radius_pos amplitudePositive frequencyPositive ratioPositive index
  have actualWeight : weight ≤ coefficient * scales.omega index := by
    have strainBound := strainSmall.trans omegaLarge
    dsimp only [coefficient]
    nlinarith
  have radiusSquare := scales.radius_sq amplitudePositive frequencyPositive ratioPositive index
  rw [amplitudeIdentity] at radiusSquare
  have geometric := EulerNonuniqueness.General.quartic_geometric_ratio_le
    (by linarith : 1 ≤ scaleRoot) omegaLarge radiusPositive.le lengthPositive radiusSquare
  have materialIdentity : scales.circulation index * weight / (scales.length index / 400) ^ 2 =
      320000 * Real.pi * scales.omega index * weight := by
    unfold Scales.circulation
    field_simp [lengthPositive.ne']
    <;> ring
  have squaredWeight := pow_le_pow_left₀ weightNonnegative actualWeight 2
  have materialWeight := mul_le_mul_of_nonneg_left actualWeight
    (by positivity : 0 ≤ 320000 * Real.pi * scales.omega index)
  refine ⟨actualWeight.trans (mul_le_mul_of_nonneg_right weightCoefficient omegaPositive.le),
    by positivity, geometric.trans ?_, ?_⟩
  · exact div_le_div_of_nonneg_right ratioCoefficient (by positivity)
  · rw [materialIdentity]
    have actual := add_le_add squaredWeight materialWeight
    have enlarged := mul_le_mul_of_nonneg_right materialCoefficient (sq_nonneg (scales.omega index))
    exact actual.trans (by convert enlarged using 1 <;> ring)

end EulerNonuniqueness.Paper
