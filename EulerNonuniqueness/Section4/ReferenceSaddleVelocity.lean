import EulerNonuniqueness.Section6.NonlinearShape

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_reference_saddle_velocity_bound :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
      ∀ {omega length difference unstable stable forcingBound : ℝ} (forcing : ℝ × ℝ),
      0 < omega → 0 < length → length ^ 2 / 2 ≤ difference → difference ≤ 2 * length ^ 2 →
      |unstable| + |stable| < radius → ‖forcing‖ ≤ forcingBound →
      let frequency := omega * length ^ 2 / difference
      let rate := 2 * Real.sqrt 2 * frequency
      let velocity := shapeChartVelocity frequency (unstable, stable) + forcing
      omega ≤ rate ∧
        |velocity.1 - rate * unstable| + |velocity.2 + rate * stable| ≤
          bound * omega * (|unstable| + |stable|) ^ 2 + 2 * forcingBound := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    shapeChartVelocity_uniform_quadratic_remainder
  refine ⟨2 * bound, by positivity, radius, radiusPositive, ?_⟩
  intro omega length difference unstable stable forcingBound forcing omegaPositive lengthPositive differenceLower
    differenceUpper small forcingBounded
  dsimp only
  have differencePositive : 0 < difference := (by positivity : 0 < length ^ 2 / 2).trans_le differenceLower
  have frequencyPositive : 0 < omega * length ^ 2 / difference := by positivity
  have frequencyLower : omega / 2 ≤ omega * length ^ 2 / difference := by
    apply (le_div_iff₀ differencePositive).mpr
    nlinarith
  have frequencyUpper : omega * length ^ 2 / difference ≤ 2 * omega := by
    apply (div_le_iff₀ differencePositive).mpr
    nlinarith
  have rootLower : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have actual := estimate (omega * length ^ 2 / difference) unstable stable small
  rw [abs_of_pos frequencyPositive] at actual
  have firstForce : |forcing.1| ≤ forcingBound :=
    (show |forcing.1| ≤ ‖forcing‖ from by simpa only [Real.norm_eq_abs] using norm_fst_le forcing).trans forcingBounded
  have secondForce : |forcing.2| ≤ forcingBound :=
    (show |forcing.2| ≤ ‖forcing‖ from by simpa only [Real.norm_eq_abs] using norm_snd_le forcing).trans forcingBounded
  constructor
  · nlinarith
  · have firstTriangle := abs_add_le
      ((shapeChartVelocity (omega * length ^ 2 / difference) (unstable, stable)).1 -
        2 * Real.sqrt 2 * (omega * length ^ 2 / difference) * unstable) forcing.1
    have secondTriangle := abs_add_le
      ((shapeChartVelocity (omega * length ^ 2 / difference) (unstable, stable)).2 +
        2 * Real.sqrt 2 * (omega * length ^ 2 / difference) * stable) forcing.2
    have nonlinearBound := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left frequencyUpper boundNonnegative) (sq_nonneg (|unstable| + |stable|))
    have firstIdentity : (shapeChartVelocity (omega * length ^ 2 / difference) (unstable, stable)).1 -
        2 * Real.sqrt 2 * (omega * length ^ 2 / difference) * unstable + forcing.1 =
      (shapeChartVelocity (omega * length ^ 2 / difference) (unstable, stable) + forcing).1 -
        (2 * Real.sqrt 2 * (omega * length ^ 2 / difference)) * unstable := by
      dsimp only [Prod.fst_add]
      ring
    have secondIdentity : (shapeChartVelocity (omega * length ^ 2 / difference) (unstable, stable)).2 +
        2 * Real.sqrt 2 * (omega * length ^ 2 / difference) * stable + forcing.2 =
      (shapeChartVelocity (omega * length ^ 2 / difference) (unstable, stable) + forcing).2 +
        (2 * Real.sqrt 2 * (omega * length ^ 2 / difference)) * stable := by
      dsimp only [Prod.snd_add]
      ring
    rw [firstIdentity] at firstTriangle
    rw [secondIdentity] at secondTriangle
    linarith

end EulerNonuniqueness.Paper
