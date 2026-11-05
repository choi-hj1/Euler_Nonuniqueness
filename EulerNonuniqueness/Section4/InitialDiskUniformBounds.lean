import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

theorem reference_rhombusRatio_bounds : 0 < rhombusRatio ∧ rhombusRatio ≤ 1 / 4 := by
  have square := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have nonnegative := Real.sqrt_nonneg (2 : ℝ)
  dsimp only [rhombusRatio]
  constructor <;> nlinarith

theorem initialDiagonal_denominator_bound {unstable : ℝ} (small : |unstable| ≤ 1) :
    1 / 2 ≤ Real.sqrt (1 - rhombusRatio * (1 + unstable)) := by
  have unstableBounds := abs_le.mp small
  have numeratorBound : rhombusRatio * (1 + unstable) ≤ 1 / 2 := by
    nlinarith [reference_rhombusRatio_bounds.1, reference_rhombusRatio_bounds.2]
  apply Real.le_sqrt_of_sq_le
  nlinarith

theorem initialDiagonals_norm_bound (scales : Scales) (index : ℕ) (phase unstable : ℝ)
    (small : |unstable| ≤ 1) :
    ‖initialPositiveDiagonal scales index phase unstable‖ ≤ 2 * scales.length index ∧
      ‖initialNegativeDiagonal scales index phase unstable‖ ≤ 2 * scales.length index := by
  have denominatorBound := initialDiagonal_denominator_bound small
  have denominatorPositive : 0 < Real.sqrt (1 - rhombusRatio * (1 + unstable)) := by linarith
  have lengthPositive := scales.length_pos index
  have numeratorNonnegative : 0 ≤ rhombusRatio * (1 + unstable) :=
    mul_nonneg reference_rhombusRatio_bounds.1.le (by linarith [(abs_le.mp small).1])
  have numeratorBound : Real.sqrt (rhombusRatio * (1 + unstable)) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    nlinarith [reference_rhombusRatio_bounds.1, reference_rhombusRatio_bounds.2,
      (abs_le.mp small).2]
  have rotationNorm (angle : ℝ) : ‖Complex.exp (Complex.I * (angle : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  constructor
  · rw [initialPositiveDiagonal, norm_div, norm_mul, rotationNorm, mul_one,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg lengthPositive.le,
      Real.norm_of_nonneg denominatorPositive.le]
    apply (div_le_iff₀ denominatorPositive).mpr
    nlinarith
  · rw [initialNegativeDiagonal, norm_mul, rotationNorm, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg (mul_nonneg lengthPositive.le (Real.sqrt_nonneg _)) denominatorPositive.le)]
    apply (div_le_iff₀ denominatorPositive).mpr
    nlinarith [Real.sqrt_nonneg (rhombusRatio * (1 + unstable))]

theorem initialDiskCenter_norm_le_three (scales : Scales) (index : ℕ) (phase unstable : ℝ)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (small : |unstable| ≤ 1) (patch : Fin 4) :
    ‖initialDiskCenter scales index phase unstable patch‖ ≤ 3 := by
  have positiveBound := (initialDiagonals_norm_bound scales index phase unstable small).1
  have negativeBound := (initialDiagonals_norm_bound scales index phase unstable small).2
  have locationNorm : ‖(scales.location index : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (scales.location_pos index).le]
    exact scales.location_le_one index
  have diagonalBound :
      ‖if patch = 0 then initialPositiveDiagonal scales index phase unstable
        else if patch = 1 then -initialPositiveDiagonal scales index phase unstable
        else if patch = 2 then initialNegativeDiagonal scales index phase unstable
        else -initialNegativeDiagonal scales index phase unstable‖ ≤ 2 := by
    split_ifs <;> (try rw [norm_neg]) <;>
      linarith [scales.length_le_one frequencyPositive ratioPositive index]
  exact (norm_add_le _ _).trans (by linarith)

theorem reference_initial_disks_uniform_support (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioBound : 1 ≤ scales.ratio) (index : ℕ) (phase unstable : ℝ)
    (small : |unstable| ≤ 1) (patch : Fin 4) :
    Metric.ball (initialDiskCenter scales index phase unstable patch) (scales.radius index) ⊆
      Metric.closedBall (0 : Plane) (3 + Real.sqrt (2 / (scales.amplitude * scales.frequency ^ 3))) := by
  intro position inside
  rw [Metric.mem_closedBall, dist_zero_right]
  have positionBound : ‖position‖ ≤ ‖position - initialDiskCenter scales index phase unstable patch‖ +
      ‖initialDiskCenter scales index phase unstable patch‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      (position - initialDiskCenter scales index phase unstable patch)
      (initialDiskCenter scales index phase unstable patch)
  have nearby : ‖position - initialDiskCenter scales index phase unstable patch‖ < scales.radius index :=
    by simpa only [Metric.mem_ball, dist_eq_norm] using inside
  linarith [initialDiskCenter_norm_le_three scales index phase unstable frequencyPositive
    (zero_lt_one.trans_le ratioBound) small patch,
    scales.radius_uniform_bound amplitudePositive frequencyPositive ratioBound index]

end EulerNonuniqueness.Paper
