import EulerNonuniqueness.Section4.ReferenceConfinement
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

def halfDiagonalRatioFromShape (point : ℝ × ℝ) : ℂ :=
  (Real.sqrt (rhombusRatio * (1 + point.1 + point.2)) : ℂ) *
    Complex.exp ((((Real.pi + Real.sqrt 2 * (point.1 - point.2)) / 2 : ℝ) : ℂ) * Complex.I)

theorem halfDiagonalRatioFromShape_continuous : Continuous halfDiagonalRatioFromShape := by
  unfold halfDiagonalRatioFromShape
  fun_prop

theorem halfDiagonalRatioFromShape_reconstruct (positive negative : ℂ)
    (positiveNonzero : positive ≠ 0) :
    halfDiagonalRatioFromShape
      (((‖negative‖ ^ 2 / ‖positive‖ ^ 2 - rhombusRatio) / rhombusRatio +
          (2 * Complex.arg (negative / positive) - Real.pi) / Real.sqrt 2) / 2,
        ((‖negative‖ ^ 2 / ‖positive‖ ^ 2 - rhombusRatio) / rhombusRatio -
          (2 * Complex.arg (negative / positive) - Real.pi) / Real.sqrt 2) / 2) = negative / positive := by
  have ratioNonzero : rhombusRatio ≠ 0 := ne_of_gt reference_rhombusRatio_bounds.1
  have sqrtNonzero : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have radialIdentity (radial angle : ℝ) :
      rhombusRatio * (1 + (radial + angle) / 2 + (radial - angle) / 2) = rhombusRatio * (1 + radial) := by ring
  have angularIdentity (radial angle : ℝ) :
      Real.pi + Real.sqrt 2 * ((radial + angle) / 2 - (radial - angle) / 2) = Real.pi + Real.sqrt 2 * angle := by ring
  unfold halfDiagonalRatioFromShape
  rw [radialIdentity, angularIdentity]
  have radiusIdentity : rhombusRatio * (1 + (‖negative‖ ^ 2 / ‖positive‖ ^ 2 - rhombusRatio) / rhombusRatio) =
      ‖negative / positive‖ ^ 2 := by
    rw [norm_div, div_pow]
    field_simp
    <;> ring
  have phaseIdentity : (Real.pi + Real.sqrt 2 *
      ((2 * Complex.arg (negative / positive) - Real.pi) / Real.sqrt 2)) / 2 = Complex.arg (negative / positive) := by
    field_simp
    <;> ring
  rw [radiusIdentity, phaseIdentity, Real.sqrt_sq (norm_nonneg _)]
  exact Complex.norm_mul_exp_arg_mul_I _

theorem halfDiagonalRatioFromShape_paper {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (positiveNonzero : positiveHalfDiagonal motion time index ≠ 0) :
    halfDiagonalRatioFromShape (unstableShape motion time index, stableShape motion time index) =
      negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index :=
  halfDiagonalRatioFromShape_reconstruct _ _ positiveNonzero

theorem halfDiagonalAmplitude_reconstruct (positive negative : ℂ) {length : ℝ}
    (lengthPositive : 0 < length) (differencePositive : 0 < ‖positive‖ ^ 2 - ‖negative‖ ^ 2) :
    Real.sqrt (((‖positive‖ ^ 2 - ‖negative‖ ^ 2) / length ^ 2) /
      (1 - ‖negative / positive‖ ^ 2)) = ‖positive‖ / length := by
  have positiveNorm : 0 < ‖positive‖ := by nlinarith [sq_nonneg ‖negative‖, norm_nonneg positive]
  have ratioIdentity : 1 - ‖negative / positive‖ ^ 2 =
      (‖positive‖ ^ 2 - ‖negative‖ ^ 2) / ‖positive‖ ^ 2 := by
    rw [norm_div, div_pow]
    field_simp
    <;> ring
  rw [ratioIdentity]
  have identity : ((‖positive‖ ^ 2 - ‖negative‖ ^ 2) / length ^ 2) /
      ((‖positive‖ ^ 2 - ‖negative‖ ^ 2) / ‖positive‖ ^ 2) = (‖positive‖ / length) ^ 2 := by
    field_simp
    <;> ring
  rw [identity, Real.sqrt_sq (div_nonneg positiveNorm.le lengthPositive.le)]

theorem halfDiagonalRatio_norm_lt_one (positive negative : ℂ)
    (differencePositive : 0 < ‖positive‖ ^ 2 - ‖negative‖ ^ 2) :
    ‖negative / positive‖ < 1 := by
  have positiveNorm : 0 < ‖positive‖ := by nlinarith [sq_nonneg ‖negative‖, norm_nonneg positive]
  rw [norm_div]
  apply (div_lt_one positiveNorm).mpr
  nlinarith [norm_nonneg negative]

end EulerNonuniqueness.Section6
