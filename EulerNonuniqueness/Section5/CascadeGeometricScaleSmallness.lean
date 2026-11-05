import EulerNonuniqueness.Section1.UniformInitialScaleSmallness

noncomputable section

open Filter

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_geometric_scale_smallness (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {factor bound : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) (boundThree : 3 ≤ bound) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      let changed : Scales := {scales with frequency := frequency}
      bound * changed.length index ≤ changed.location index / 200 ∧
      changed.radius index ≤ factor * changed.length index / 1000 ∧
      changed.length index ≤ changed.location index / 1000 ∧
      changed.radius index ≤ changed.location index / 1000 := by
  have boundPositive : 0 < bound := by linarith
  have tolerancePositive : 0 < min (1 / 1000 : ℝ) (1 / (200 * bound)) := by positivity
  filter_upwards [scales.eventually_length_lt_location ratioBound alphaPositive tolerancePositive,
    scales.eventually_radius_lt_length amplitudePositive (show 1 ≤ scales.ratio by linarith)
      (show 0 < factor / 1000 by positivity)] with frequency lengths radii index
  let changed : Scales := {scales with frequency := frequency}
  have locationPositive := changed.location_pos index
  have lengthPositive := changed.length_pos index
  have lengthBound : changed.length index ≤ changed.location index / 1000 := by
    have estimate := (lengths index).le.trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _) locationPositive.le)
    simpa only [one_div, inv_mul_eq_div] using estimate
  have weightedLength : bound * changed.length index ≤ changed.location index / 200 := by
    have estimate := (lengths index).le.trans
      (mul_le_mul_of_nonneg_right (min_le_right _ _) locationPositive.le)
    calc
      _ ≤ bound * ((1 / (200 * bound)) * changed.location index) :=
        mul_le_mul_of_nonneg_left estimate boundPositive.le
      _ = _ := by field_simp; ring
  have radiusBound : changed.radius index ≤ factor * changed.length index / 1000 := by
    simpa only [div_mul_eq_mul_div] using (radii index).le
  have factorLength : factor * changed.length index ≤ changed.length index :=
    mul_le_of_le_one_left lengthPositive.le factorSmall
  refine ⟨weightedLength, radiusBound, lengthBound, ?_⟩
  have weakLength : changed.length index ≤ changed.location index := by linarith
  linarith

end EulerNonuniqueness.Paper
