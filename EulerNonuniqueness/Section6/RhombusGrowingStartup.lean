import EulerNonuniqueness.Section6.RhombusStrain

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem idealGrowingInput_prefix_error {frequency coefficient time : ℝ}
    (frequencyNonnegative : 0 ≤ frequency) (coefficientNonnegative : 0 ≤ coefficient)
    (timeNonnegative : 0 ≤ time) :
    |(∫ current in (0 : ℝ)..time, Real.exp (-(2 * Real.sqrt 2 * frequency) * current) *
        idealGrowingInput frequency coefficient current) - coefficient| ≤
      coefficient * (Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
        (1 + 2 * Real.sqrt 3 * frequency * time)) := by
  have response := idealGrowingResponse_error frequency coefficient 0 time frequencyNonnegative coefficientNonnegative timeNonnegative
  have identity : (∫ current in (0 : ℝ)..time, Real.exp (-(2 * Real.sqrt 2 * frequency) * current) *
      idealGrowingInput frequency coefficient current) - coefficient =
      Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
        (idealGrowingResponse frequency coefficient 0 time - coefficient * Real.exp (2 * Real.sqrt 2 * frequency * time)) := by
    rw [idealGrowingInput_integral _ _ _ timeNonnegative]
    dsimp only [idealGrowingResponse]
    simp only [zero_add]
    ring
  rw [identity, abs_mul, abs_of_pos (Real.exp_pos _)]
  have actual := mul_le_mul_of_nonneg_left response (Real.exp_pos (-(2 * Real.sqrt 2 * frequency) * time)).le
  simpa only [zero_add, mul_assoc, mul_comm, mul_left_comm] using actual

theorem exists_uniform_rotating_rhombus_startup :
    ∃ startup > (0 : ℝ), ∀ {frequency coefficient time : ℝ},
      0 < frequency → 0 ≤ coefficient → 0 ≤ time → startup ≤ frequency * time →
      (7 / 8 : ℝ) * coefficient ≤
        ∫ current in (0 : ℝ)..time, Real.exp (-(2 * Real.sqrt 2 * frequency) * current) *
          idealGrowingInput frequency coefficient current := by
  have small := (exponential_affine_decay (by positivity : (0 : ℝ) < 2 * Real.sqrt 2) 1 (2 * Real.sqrt 3)).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  obtain ⟨startup, eventuallySmall⟩ := eventually_atTop.mp small
  refine ⟨max 1 startup, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro frequency coefficient time frequencyPositive coefficientNonnegative timeNonnegative afterStartup
  have scalar := eventuallySmall (frequency * time) ((le_max_right _ _).trans afterStartup)
  have exponentialBound : Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      (1 + 2 * Real.sqrt 3 * frequency * time) ≤ 1 / 8 := by
    convert scalar.le using 1 <;> congr 2 <;> ring
  have actual := (idealGrowingInput_prefix_error frequencyPositive.le coefficientNonnegative timeNonnegative).trans
    (mul_le_mul_of_nonneg_left exponentialBound coefficientNonnegative)
  linarith only [(abs_le.mp actual).1]

end EulerNonuniqueness.Section6
