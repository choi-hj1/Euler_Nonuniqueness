import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace EulerNonuniqueness.General

theorem quartic_frequency_forcing_scale
    {forcingConstant scaleRoot frequency : ℝ}
    (forcingNonnegative : 0 ≤ forcingConstant) (rootPositive : 0 < scaleRoot)
    (frequencyPositive : 0 < frequency) :
    (forcingConstant * frequency / (scaleRoot ^ 3 * frequency ^ 4)) ^ 2 ≤
      ((forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)) ^ 3 := by
  have coefficient : forcingConstant ^ 2 ≤ (forcingConstant + 1) ^ 3 := by
    nlinarith [sq_nonneg forcingConstant, pow_nonneg forcingNonnegative 3]
  have commonPositive : 0 < scaleRoot ^ 6 * frequency ^ 6 := by positivity
  have scaled := (div_le_div_iff_of_pos_right commonPositive).2 coefficient
  convert scaled using 1 <;> field_simp <;> ring

theorem quartic_frequency_confinement_budget
    {forcingConstant scaleRoot frequency normalConstant terminal : ℝ}
    (rootNonzero : scaleRoot ≠ 0) (frequencyNonzero : frequency ≠ 0) :
    8 * normalConstant * ((scaleRoot ^ 3 * frequency ^ 4) * terminal) *
        ((forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)) ^ 2 =
      8 * normalConstant * terminal * (forcingConstant + 1) ^ 2 / scaleRoot := by
  field_simp
  <;> ring

theorem quartic_frequency_primitive_small
    {forcingConstant scaleRoot frequency : ℝ}
    (forcingNonnegative : 0 ≤ forcingConstant) (rootLarge : 8 ≤ scaleRoot)
    (frequencyLarge : 1 ≤ frequency) :
    forcingConstant * frequency / (scaleRoot ^ 3 * frequency ^ 4) ≤
      ((forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)) / 8 := by
  have rootPositive : 0 < scaleRoot := by linarith
  have frequencyPositive : 0 < frequency := by linarith
  have first : 8 * forcingConstant ≤ scaleRoot * (forcingConstant + 1) := by
    nlinarith
  have second : scaleRoot * (forcingConstant + 1) ≤
      scaleRoot * (forcingConstant + 1) * frequency := by
    have weighted := mul_le_mul_of_nonneg_left frequencyLarge
      (show 0 ≤ scaleRoot * (forcingConstant + 1) by positivity)
    simpa using weighted
  apply (div_le_iff₀ (by positivity : 0 < scaleRoot ^ 3 * frequency ^ 4)).2
  have scaled := mul_le_mul_of_nonneg_right (first.trans second) frequencyPositive.le
  have divided := div_le_div_of_nonneg_right scaled (by norm_num : (0 : ℝ) ≤ 8)
  convert divided using 1
  · ring
  · field_simp [rootPositive.ne', frequencyPositive.ne']
    <;> ring

theorem exists_quartic_frequency_cubic_budget
    {forcingConstant normalConstant terminal neutralRadius amplitudeThreshold : ℝ}
    (forcingNonnegative : 0 ≤ forcingConstant) (neutralRadiusPositive : 0 < neutralRadius) :
    ∃ scaleRoot : ℝ, 8 ≤ scaleRoot ∧ amplitudeThreshold < scaleRoot ^ 3 ∧
      ∀ frequency : ℝ, 1 ≤ frequency →
        let strength := scaleRoot ^ 3 * frequency ^ 4
        let epsilon := forcingConstant * frequency / strength
        let radius := (forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)
        0 < radius ∧ radius ≤ 1 ∧ epsilon ^ 2 ≤ radius ^ 3 ∧
          epsilon ≤ radius / 8 ∧
          8 * normalConstant * (strength * terminal) * radius ^ 2 < min 1 neutralRadius := by
  let budget := min 1 neutralRadius
  have budgetPositive : 0 < budget := lt_min (by norm_num) neutralRadiusPositive
  obtain ⟨scaleRoot, rootLarge⟩ := exists_gt
    (max (max 8 (max (forcingConstant + 1) amplitudeThreshold))
      (8 * normalConstant * terminal * (forcingConstant + 1) ^ 2 / budget))
  have rootEight : 8 < scaleRoot :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) rootLarge
  have rootCoefficient : forcingConstant + 1 < scaleRoot := by
    exact lt_of_le_of_lt (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) rootLarge
  have rootThreshold : amplitudeThreshold < scaleRoot := by
    exact lt_of_le_of_lt (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) rootLarge
  have rootBudget : 8 * normalConstant * terminal * (forcingConstant + 1) ^ 2 / budget < scaleRoot :=
    (le_max_right _ _).trans_lt rootLarge
  have rootPositive : 0 < scaleRoot := by linarith
  have rootSquare : scaleRoot ≤ scaleRoot ^ 2 := by nlinarith
  have rootCube : scaleRoot ≤ scaleRoot ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left rootSquare rootPositive.le]
  refine ⟨scaleRoot, rootEight.le, rootThreshold.trans_le rootCube, ?_⟩
  intro frequency frequencyLarge
  have frequencyPositive : 0 < frequency := by linarith
  have frequencySquare : 1 ≤ frequency ^ 2 := by nlinarith
  have radiusSmall : (forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2) ≤ 1 := by
    apply (div_le_one₀ (by positivity : 0 < scaleRoot ^ 2 * frequency ^ 2)).2
    exact rootCoefficient.le.trans (rootSquare.trans (by nlinarith [sq_nonneg scaleRoot]))
  refine ⟨by positivity, radiusSmall,
    quartic_frequency_forcing_scale forcingNonnegative rootPositive frequencyPositive,
    quartic_frequency_primitive_small forcingNonnegative rootEight.le frequencyLarge, ?_⟩
  rw [quartic_frequency_confinement_budget rootPositive.ne' frequencyPositive.ne']
  apply (div_lt_iff₀ rootPositive).2
  have multiplied := (div_lt_iff₀ budgetPositive).1 rootBudget
  simpa only [budget, mul_comm] using multiplied

theorem exists_quartic_frequency_cubic_budget_for_all_large_amplitudes
    {forcingConstant normalConstant terminal neutralRadius : ℝ}
    (forcingNonnegative : 0 ≤ forcingConstant) (normalNonnegative : 0 ≤ normalConstant)
    (terminalNonnegative : 0 ≤ terminal) (neutralRadiusPositive : 0 < neutralRadius) :
    ∃ amplitudeMin > (0 : ℝ), ∀ amplitude : ℝ, amplitudeMin ≤ amplitude →
      ∃ scaleRoot > (0 : ℝ), scaleRoot ^ 3 = amplitude ∧
      ∀ frequency : ℝ, 1 ≤ frequency →
        let strength := amplitude * frequency ^ 4
        let epsilon := forcingConstant * frequency / strength
        let radius := (forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)
        0 < radius ∧ radius ≤ 1 ∧ epsilon ^ 2 ≤ radius ^ 3 ∧
          epsilon ≤ radius / 8 ∧
          8 * normalConstant * (strength * terminal) * radius ^ 2 < min 1 neutralRadius := by
  obtain ⟨baseRoot, baseEight, _, baseBounds⟩ :=
    exists_quartic_frequency_cubic_budget (amplitudeThreshold := 0)
      (normalConstant := normalConstant) (terminal := terminal)
      forcingNonnegative neutralRadiusPositive
  have basePositive : 0 < baseRoot := by linarith
  refine ⟨baseRoot ^ 3, by positivity, ?_⟩
  intro amplitude amplitudeLarge
  have amplitudePositive : 0 < amplitude := (by positivity : 0 < baseRoot ^ 3).trans_le amplitudeLarge
  let scaleRoot := amplitude ^ ((3 : ℝ)⁻¹)
  have rootPositive : 0 < scaleRoot := Real.rpow_pos_of_pos amplitudePositive _
  have cube : scaleRoot ^ 3 = amplitude :=
    Real.rpow_inv_natCast_pow amplitudePositive.le (by norm_num : (3 : ℕ) ≠ 0)
  have rootLarge : baseRoot ≤ scaleRoot := by
    apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp
    rwa [cube]
  have rootEight : 8 ≤ scaleRoot := baseEight.trans rootLarge
  refine ⟨scaleRoot, rootPositive, cube, ?_⟩
  intro frequency frequencyLarge
  have frequencyPositive : 0 < frequency := by linarith
  obtain ⟨_, baseRadiusSmall, _, _, baseBudget⟩ := baseBounds frequency frequencyLarge
  have denominatorOrder : baseRoot ^ 2 * frequency ^ 2 ≤ scaleRoot ^ 2 * frequency ^ 2 := by
    gcongr
  have radiusSmall : (forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2) ≤ 1 :=
    (div_le_div_of_nonneg_left (by linarith : 0 ≤ forcingConstant + 1)
      (by positivity : 0 < baseRoot ^ 2 * frequency ^ 2) denominatorOrder).trans baseRadiusSmall
  dsimp only
  rw [← cube]
  refine ⟨by positivity, radiusSmall,
    quartic_frequency_forcing_scale forcingNonnegative rootPositive frequencyPositive,
    quartic_frequency_primitive_small forcingNonnegative rootEight frequencyLarge, ?_⟩
  rw [quartic_frequency_confinement_budget rootPositive.ne' frequencyPositive.ne']
  rw [quartic_frequency_confinement_budget basePositive.ne' frequencyPositive.ne'] at baseBudget
  exact (div_le_div_of_nonneg_left (by positivity : 0 ≤
    8 * normalConstant * terminal * (forcingConstant + 1) ^ 2) basePositive rootLarge).trans_lt baseBudget

end EulerNonuniqueness.General
