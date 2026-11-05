import EulerNonuniqueness.General.QuarticMaterialScaleChoice

namespace EulerNonuniqueness.General

theorem quartic_frequency_numerator_ratio
    {forcingConstant scaleRoot frequency numerator : ℝ}
    (forcingNonnegative : 0 ≤ forcingConstant) (rootPositive : 0 < scaleRoot)
    (frequencyPositive : 0 < frequency) (numeratorBound : numerator ≤ forcingConstant * frequency ^ 2) :
    numerator / (scaleRoot ^ 3 * frequency ^ 4) ≤
      (forcingConstant / scaleRoot) * ((forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)) := by
  apply (div_le_iff₀ (by positivity : 0 < scaleRoot ^ 3 * frequency ^ 4)).mpr
  have numerical : numerator ≤ forcingConstant * (forcingConstant + 1) * frequency ^ 2 := by
    have extra : 0 ≤ forcingConstant ^ 2 * frequency ^ 2 := by positivity
    nlinarith
  convert numerical using 1 <;> field_simp [rootPositive.ne', frequencyPositive.ne'] <;> ring

theorem quartic_material_normal_form_budget
    {forcingConstant initialConstant normalConstant terminal scaleRoot frequency weight geometricRatio numerator : ℝ}
    (forcingNonnegative : 0 ≤ forcingConstant) (initialNonnegative : 0 ≤ initialConstant)
    (normalNonnegative : 0 ≤ normalConstant) (terminalNonnegative : 0 ≤ terminal)
    (rootLarge : 8 ≤ scaleRoot) (frequencyLarge : 1 ≤ frequency)
    (weightBound : weight ≤ forcingConstant * frequency) (ratioNonnegative : 0 ≤ geometricRatio)
    (ratioBound : geometricRatio ≤ forcingConstant / (scaleRoot * frequency))
    (numeratorBound : numerator ≤ forcingConstant * frequency ^ 2) :
    let strength := scaleRoot ^ 3 * frequency ^ 4
    let radius := (forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)
    initialConstant * (weight / strength) + normalConstant * terminal *
        (strength * radius ^ 3 + weight * radius ^ 2 + weight * geometricRatio * radius + numerator / strength) ≤
      ((initialConstant * forcingConstant + normalConstant * terminal *
        ((forcingConstant + 1) ^ 2 + forcingConstant * (forcingConstant + 1) + forcingConstant ^ 2 + forcingConstant)) / scaleRoot) * radius := by
  let strength := scaleRoot ^ 3 * frequency ^ 4
  let radius := (forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)
  have rootPositive : 0 < scaleRoot := by linarith
  have frequencyPositive : 0 < frequency := by linarith
  have radiusNonnegative : 0 ≤ radius := by dsimp [radius]; positivity
  have weightNumerator : weight ≤ forcingConstant * frequency ^ 2 := by
    have square : frequency ≤ frequency ^ 2 := by nlinarith
    exact weightBound.trans (mul_le_mul_of_nonneg_left square forcingNonnegative)
  have initialBound := quartic_frequency_numerator_ratio forcingNonnegative rootPositive frequencyPositive weightNumerator
  have amplitudeBound := quartic_frequency_numerator_ratio forcingNonnegative rootPositive frequencyPositive numeratorBound
  have selfIdentity : strength * radius ^ 2 = (forcingConstant + 1) ^ 2 / scaleRoot :=
    quartic_frequency_cubic_ratio rootPositive.ne' frequencyPositive.ne'
  have weightRatio : weight * radius ≤ forcingConstant * (forcingConstant + 1) / scaleRoot :=
    (mul_le_mul_of_nonneg_right weightBound radiusNonnegative).trans
      (quartic_frequency_quadratic_forcing_ratio forcingNonnegative (by linarith) (by linarith) frequencyLarge)
  have higherRatio : weight * geometricRatio ≤ forcingConstant ^ 2 / scaleRoot := by
    have actual := (mul_le_mul_of_nonneg_right weightBound ratioNonnegative).trans
      (quartic_frequency_higher_mode_ratio forcingNonnegative frequencyPositive rootPositive ratioBound)
    simpa only [pow_two] using actual
  have selfBound : strength * radius ^ 3 = ((forcingConstant + 1) ^ 2 / scaleRoot) * radius := by
    calc
      _ = (strength * radius ^ 2) * radius := by ring
      _ = _ := by rw [selfIdentity]
  have quadraticBound : weight * radius ^ 2 ≤ (forcingConstant * (forcingConstant + 1) / scaleRoot) * radius := by
    have actual := mul_le_mul_of_nonneg_right weightRatio radiusNonnegative
    convert actual using 1 <;> ring
  have higherBound := mul_le_mul_of_nonneg_right higherRatio radiusNonnegative
  have errorBound := add_le_add
    (add_le_add (add_le_add (le_of_eq selfBound) quadraticBound) higherBound) amplitudeBound
  have actual := add_le_add (mul_le_mul_of_nonneg_left initialBound initialNonnegative)
    (mul_le_mul_of_nonneg_left errorBound (mul_nonneg normalNonnegative terminalNonnegative))
  change initialConstant * (weight / strength) + normalConstant * terminal *
    (strength * radius ^ 3 + weight * radius ^ 2 + weight * geometricRatio * radius + numerator / strength) ≤ _
  exact actual.trans_eq (by ring)

theorem exists_uniform_quartic_material_budget_root
    {forcingConstant initialConstant normalConstant terminal : ℝ}
    (forcingNonnegative : 0 ≤ forcingConstant) (initialNonnegative : 0 ≤ initialConstant)
    (normalNonnegative : 0 ≤ normalConstant) (terminalNonnegative : 0 ≤ terminal) :
    ∃ rootMin ≥ (8 : ℝ), ∀ scaleRoot : ℝ, rootMin ≤ scaleRoot →
      ∀ frequency : ℝ, 1 ≤ frequency → ∀ weight geometricRatio numerator : ℝ,
      weight ≤ forcingConstant * frequency → 0 ≤ geometricRatio →
      geometricRatio ≤ forcingConstant / (scaleRoot * frequency) → numerator ≤ forcingConstant * frequency ^ 2 →
      let strength := scaleRoot ^ 3 * frequency ^ 4
      let radius := (forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)
      initialConstant * (weight / strength) + normalConstant * terminal *
          (strength * radius ^ 3 + weight * radius ^ 2 + weight * geometricRatio * radius + numerator / strength) < radius / 8 := by
  let budget := initialConstant * forcingConstant + normalConstant * terminal *
    ((forcingConstant + 1) ^ 2 + forcingConstant * (forcingConstant + 1) + forcingConstant ^ 2 + forcingConstant)
  let rootMin := max 8 (8 * budget + 1)
  refine ⟨rootMin, le_max_left _ _, ?_⟩
  intro scaleRoot rootLarge frequency frequencyLarge weight geometricRatio numerator weightBound ratioNonnegative ratioBound numeratorBound
  have rootEight : 8 ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have rootPositive : 0 < scaleRoot := by linarith
  have frequencyPositive : 0 < frequency := by linarith
  have budgetStrict : 8 * budget < scaleRoot := by
    have actual := (le_max_right (8 : ℝ) (8 * budget + 1)).trans rootLarge
    linarith
  have ratioStrict : budget / scaleRoot < 1 / 8 := by
    apply (div_lt_iff₀ rootPositive).mpr
    have actual : budget < scaleRoot / 8 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
      (by simpa only [mul_comm] using budgetStrict)
    convert actual using 1 <;> ring
  have radiusPositive : 0 < (forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2) := by positivity
  have actual := quartic_material_normal_form_budget forcingNonnegative initialNonnegative normalNonnegative terminalNonnegative
    rootEight frequencyLarge weightBound ratioNonnegative ratioBound numeratorBound
  exact actual.trans_lt ((mul_lt_mul_of_pos_right ratioStrict radiusPositive).trans_eq (by ring))

end EulerNonuniqueness.General
