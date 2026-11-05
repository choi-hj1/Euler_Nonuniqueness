import EulerNonuniqueness.Section4.InitialDiskUniformBounds

noncomputable section

namespace EulerNonuniqueness.Paper

theorem reference_rhombusRatio_lower : 1 / 8 ≤ rhombusRatio := by
  have square := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have positive := Real.sqrt_nonneg (2 : ℝ)
  dsimp only [rhombusRatio]
  nlinarith

theorem initialDiagonals_separation_bounds (scales : Scales) (index : ℕ) (phase unstable : ℝ)
    (small : |unstable| ≤ 1 / 2) :
    scales.length index ≤ ‖initialPositiveDiagonal scales index phase unstable‖ ∧
      scales.length index / 4 ≤ ‖initialNegativeDiagonal scales index phase unstable‖ ∧
      ‖initialNegativeDiagonal scales index phase unstable‖ ≤
        (3 / 4 : ℝ) * ‖initialPositiveDiagonal scales index phase unstable‖ := by
  let ratio := rhombusRatio * (1 + unstable)
  have ratioLower : 1 / 16 ≤ ratio := by
    dsimp only [ratio]
    nlinarith [reference_rhombusRatio_lower, reference_rhombusRatio_bounds.1, (abs_le.mp small).1]
  have ratioUpper : ratio ≤ 3 / 8 := by
    dsimp only [ratio]
    nlinarith [reference_rhombusRatio_bounds.1, reference_rhombusRatio_bounds.2, (abs_le.mp small).2]
  have numeratorLower : 1 / 4 ≤ Real.sqrt ratio := Real.le_sqrt_of_sq_le (by nlinarith)
  have numeratorUpper : Real.sqrt ratio ≤ 3 / 4 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have denominatorLower : 1 / 2 ≤ Real.sqrt (1 - ratio) := Real.le_sqrt_of_sq_le (by linarith)
  have denominatorUpper : Real.sqrt (1 - ratio) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have denominatorPositive : 0 < Real.sqrt (1 - ratio) := by linarith
  have lengthPositive := scales.length_pos index
  have rotationNorm (angle : ℝ) : ‖Complex.exp (Complex.I * (angle : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have positiveNorm : ‖initialPositiveDiagonal scales index phase unstable‖ =
      scales.length index / Real.sqrt (1 - ratio) := by
    rw [initialPositiveDiagonal, norm_div, norm_mul, rotationNorm, mul_one,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg lengthPositive.le,
      Real.norm_of_nonneg denominatorPositive.le]
  have negativeNorm : ‖initialNegativeDiagonal scales index phase unstable‖ =
      scales.length index * Real.sqrt ratio / Real.sqrt (1 - ratio) := by
    rw [initialNegativeDiagonal, norm_mul, rotationNorm, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg (mul_nonneg lengthPositive.le (Real.sqrt_nonneg _)) denominatorPositive.le)]
  rw [positiveNorm, negativeNorm]
  refine ⟨?_, ?_, ?_⟩
  · apply (le_div_iff₀ denominatorPositive).mpr
    nlinarith
  · apply (le_div_iff₀ denominatorPositive).mpr
    nlinarith [mul_le_mul_of_nonneg_left numeratorLower lengthPositive.le]
  · calc
      _ ≤ (scales.length index * (3 / 4)) / Real.sqrt (1 - ratio) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left numeratorUpper lengthPositive.le) denominatorPositive.le
      _ = _ := by ring

theorem initialDiskCenter_same_scale_separation (scales : Scales) (index : ℕ) (phase unstable : ℝ)
    (small : |unstable| ≤ 1 / 2) (first second : Fin 4) (different : first ≠ second) :
    scales.length index / 4 ≤
      ‖initialDiskCenter scales index phase unstable first - initialDiskCenter scales index phase unstable second‖ := by
  obtain ⟨positiveLower, negativeLower, ratioBound⟩ := initialDiagonals_separation_bounds scales index phase unstable small
  have lengthPositive := scales.length_pos index
  have positiveOpposite : scales.length index / 4 ≤
      ‖initialPositiveDiagonal scales index phase unstable - -initialPositiveDiagonal scales index phase unstable‖ := by
    rw [show initialPositiveDiagonal scales index phase unstable - -initialPositiveDiagonal scales index phase unstable =
      (2 : ℝ) • initialPositiveDiagonal scales index phase unstable by simp [two_smul, sub_neg_eq_add],
      norm_smul, Real.norm_eq_abs]
    norm_num
    linarith
  have negativeOpposite : scales.length index / 4 ≤
      ‖initialNegativeDiagonal scales index phase unstable - -initialNegativeDiagonal scales index phase unstable‖ := by
    rw [show initialNegativeDiagonal scales index phase unstable - -initialNegativeDiagonal scales index phase unstable =
      (2 : ℝ) • initialNegativeDiagonal scales index phase unstable by simp [two_smul, sub_neg_eq_add],
      norm_smul, Real.norm_eq_abs]
    norm_num
    linarith
  have mixedSub : scales.length index / 4 ≤
      ‖initialPositiveDiagonal scales index phase unstable - initialNegativeDiagonal scales index phase unstable‖ := by
    have estimate := norm_sub_norm_le (initialPositiveDiagonal scales index phase unstable)
      (initialNegativeDiagonal scales index phase unstable)
    linarith
  have mixedAdd : scales.length index / 4 ≤
      ‖initialPositiveDiagonal scales index phase unstable + initialNegativeDiagonal scales index phase unstable‖ := by
    have estimate := norm_sub_norm_le (initialPositiveDiagonal scales index phase unstable)
      (-initialNegativeDiagonal scales index phase unstable)
    rw [norm_neg, sub_neg_eq_add] at estimate
    linarith
  fin_cases first <;> fin_cases second <;>
    simp_all [initialDiskCenter, sub_neg_eq_add, neg_sub, norm_neg, norm_sub_rev, add_comm]
  · simpa only [sub_eq_add_neg] using mixedSub
  · rw [show -initialNegativeDiagonal scales index phase unstable - initialPositiveDiagonal scales index phase unstable =
      -(initialNegativeDiagonal scales index phase unstable + initialPositiveDiagonal scales index phase unstable) by abel,
      norm_neg]
    exact mixedAdd
  · rw [show -initialNegativeDiagonal scales index phase unstable + initialPositiveDiagonal scales index phase unstable =
      -(initialNegativeDiagonal scales index phase unstable - initialPositiveDiagonal scales index phase unstable) by abel,
      norm_neg]
    exact mixedSub

end EulerNonuniqueness.Paper
