import EulerNonuniqueness.Section1.Scales

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.coarse_follower_rate_gap (scales : Scales) (constant : ℝ)
    (frequencyPositive : 0 < scales.frequency) (ratioOne : 1 ≤ scales.ratio)
    (constantNonnegative : 0 ≤ constant) :
    ∀ source drive : ℕ, source < drive →
      scales.ratio * scales.omega (source + 1) ≤ scales.omega (drive + 1) ∧
      constant * scales.omega (source + 1) ≤
        (constant * scales.omega (drive + 1)) / scales.ratio ∧
      (2 * constant ≤ scales.ratio →
        (constant * scales.omega (drive + 1)) / scales.ratio ≤ scales.omega (drive + 1) / 2 ∧
        (constant * scales.omega (drive + 1)) / scales.ratio <
          2 * Real.sqrt 2 * scales.omega (drive + 1)) := by
  intro source drive below
  have ratioPositive : 0 < scales.ratio := zero_lt_one.trans_le ratioOne
  have powers : scales.ratio ^ (source + 2) ≤ scales.ratio ^ (drive + 1) :=
    pow_le_pow_right₀ ratioOne (by omega)
  have geometric : scales.ratio * scales.omega (source + 1) ≤ scales.omega (drive + 1) := by
    have actual := mul_le_mul_of_nonneg_left powers frequencyPositive.le
    calc
      scales.ratio * scales.omega (source + 1) =
          scales.frequency * scales.ratio ^ (source + 2) := by
        rw [Scales.omega, show source + 2 = (source + 1) + 1 by omega, pow_succ]
        ring
      _ ≤ scales.omega (drive + 1) := actual
  have scaled : constant * scales.omega (source + 1) ≤
      (constant * scales.omega (drive + 1)) / scales.ratio := by
    apply (le_div_iff₀ ratioPositive).mpr
    have actual := mul_le_mul_of_nonneg_left geometric constantNonnegative
    convert actual using 1
    ring
  refine ⟨geometric, scaled, ?_⟩
  intro separated
  have drivePositive := scales.omega_pos frequencyPositive ratioPositive (drive + 1)
  have halfBound : (constant * scales.omega (drive + 1)) / scales.ratio ≤
      scales.omega (drive + 1) / 2 := by
    apply (div_le_iff₀ ratioPositive).mpr
    have actual := mul_le_mul_of_nonneg_right separated drivePositive.le
    nlinarith only [actual]
  have sqrtOne : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have halfStrict : scales.omega (drive + 1) / 2 < 2 * Real.sqrt 2 * scales.omega (drive + 1) := by
    have actual := mul_le_mul_of_nonneg_right sqrtOne drivePositive.le
    nlinarith only [actual, drivePositive]
  exact ⟨halfBound, halfBound.trans_lt halfStrict⟩

end EulerNonuniqueness.Paper

