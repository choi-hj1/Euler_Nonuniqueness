import EulerNonuniqueness.Section3.C1PowerDifferenceBound

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  powerDifferenceC1Group

theorem relabeledDiskForcingPrimitive_difference_bound
    (first second : PeriodicC1HolderHalf)
    (firstBound : ‖diskRelabelCurve first 1‖ ≤ 3)
    (secondBound : ‖diskRelabelCurve second 1‖ ≤ 3)
    (degree : ℕ) {frequency : ℝ} (nonzero : frequency ≠ 0)
    (amplitude : ℝ → ℂ) (time : ℝ) :
    ‖relabeledDiskForcingPrimitive first degree frequency amplitude time -
      relabeledDiskForcingPrimitive second degree frequency amplitude time‖ ≤
      (2 / |frequency|) * ((24 : ℝ) ^ (degree + 1) * ‖amplitude time‖) *
        ‖diskRelabelCurve first 1 - diskRelabelCurve second 1‖ := by
  have conjugateDifference :
      relabeledDiskForcingMode first degree - relabeledDiskForcingMode second degree =
        c1Conjugate (c1NaturalPower (diskRelabelCurve first 1) (degree + 1) -
          c1NaturalPower (diskRelabelCurve second 1) (degree + 1)) := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    simp only [relabeledDiskForcingMode, c1Conjugate_value]
    exact (map_sub (starRingEnd ℂ) _ _).symm
  have modeBound := (c1Conjugate_norm_bound
    (c1NaturalPower (diskRelabelCurve first 1) (degree + 1) -
      c1NaturalPower (diskRelabelCurve second 1) (degree + 1))).trans
        (c1NaturalPower_difference_bound _ _ firstBound secondBound (degree + 1))
  have positiveDegree : (0 : ℝ) < (degree + 1 : ℕ) := by positivity
  have positiveFrequency : 0 < |frequency| := abs_pos.mpr nonzero
  unfold relabeledDiskForcingPrimitive
  rw [← smul_sub, norm_smul, norm_mul, norm_mul, diskForcingPhase_norm, mul_one,
    diskForcingPrimitiveFactor_norm, conjugateDifference]
  calc
    _ ≤ (2 / (((degree + 1 : ℕ) : ℝ) * |frequency|)) * ‖amplitude time‖ *
        ((degree + 1 : ℕ) * (24 : ℝ) ^ (degree + 1) *
          ‖diskRelabelCurve first 1 - diskRelabelCurve second 1‖) :=
      mul_le_mul_of_nonneg_left modeBound (by positivity)
    _ = _ := by field_simp; ring

end EulerNonuniqueness.Paper
