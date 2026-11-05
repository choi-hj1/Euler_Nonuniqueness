import Mathlib

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness.Section6

def inversePowerInnerCutoff (distance : ℝ) (position : ℂ) : ℝ :=
  Real.smoothTransition ((‖position‖ ^ 2 - (distance / 2) ^ 2) /
    ((3 * distance / 4) ^ 2 - (distance / 2) ^ 2))

def smoothConjugateInversePower (distance : ℝ) (power : ℕ) (position : ℂ) : ℂ :=
  (inversePowerInnerCutoff distance position : ℂ) * (star position)⁻¹ ^ power

theorem inversePowerInnerCutoff_contDiff (distance : ℝ) : ContDiff ℝ ∞ (inversePowerInnerCutoff distance) :=
  Real.smoothTransition.contDiff.comp (((contDiff_norm_sq ℝ).sub contDiff_const).div_const _)

theorem inversePowerInnerCutoff_zero {distance : ℝ} (positive : 0 < distance) {position : ℂ}
    (small : ‖position‖ ≤ distance / 2) : inversePowerInnerCutoff distance position = 0 := by
  have denominatorPositive : 0 < (3 * distance / 4) ^ 2 - (distance / 2) ^ 2 := by nlinarith
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ denominatorPositive.le
  nlinarith [norm_nonneg position]

theorem inversePowerInnerCutoff_one {distance : ℝ} (positive : 0 < distance) {position : ℂ}
    (large : 3 * distance / 4 ≤ ‖position‖) : inversePowerInnerCutoff distance position = 1 := by
  have denominatorPositive : 0 < (3 * distance / 4) ^ 2 - (distance / 2) ^ 2 := by nlinarith
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div denominatorPositive).mpr
  nlinarith [norm_nonneg position]

theorem smoothConjugateInversePower_contDiff {distance : ℝ} (positive : 0 < distance) (power : ℕ) :
    ContDiff ℝ ∞ (smoothConjugateInversePower distance power) := by
  apply contDiff_iff_contDiffAt.mpr
  intro position
  by_cases zero : position = 0
  · subst position
    have agrees : smoothConjugateInversePower distance power =ᶠ[𝓝 (0 : ℂ)] fun _ => (0 : ℂ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by positivity : 0 < distance / 2)] with current member
      have small : ‖current‖ ≤ distance / 2 :=
        (show ‖current‖ < distance / 2 by simpa only [Metric.mem_ball, dist_zero_right] using member).le
      simp only [smoothConjugateInversePower, inversePowerInnerCutoff_zero positive small, Complex.ofReal_zero, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq agrees
  · exact ((Complex.ofRealCLM.contDiff.comp (inversePowerInnerCutoff_contDiff distance)).contDiffAt).mul
      (((Complex.conjCLE.contDiff.contDiffAt).inv (by simpa using zero)).pow power)

theorem smoothConjugateInversePower_eventuallyEq {distance : ℝ} (positive : 0 < distance)
    (power : ℕ) {position : ℂ} (separated : distance ≤ ‖position‖) :
    smoothConjugateInversePower distance power =ᶠ[𝓝 position] fun current => (star current)⁻¹ ^ power := by
  have large : 3 * distance / 4 < ‖position‖ := by linarith
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds large] with current member
  simp only [smoothConjugateInversePower, inversePowerInnerCutoff_one positive member.le, Complex.ofReal_one, one_mul]

theorem conjugate_zpow_hasFDerivAt (power : ℤ) {position : ℂ} (nonzero : position ≠ 0) :
    HasFDerivAt (fun current : ℂ => (star current) ^ power)
      (((power : ℂ) * (star position) ^ (power - 1)) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) position := by
  have outer := (hasDerivAt_zpow power (star position) (Or.inl (by simpa using nonzero))).hasFDerivAt.restrictScalars ℝ
  have composed := outer.comp position (Complex.conjCLE.hasFDerivAt (x := position))
  convert composed using 1
  ext direction
  change ((power : ℂ) * (star position) ^ (power - 1)) * star direction =
    star direction * ((power : ℂ) * (star position) ^ (power - 1))
  ring

theorem smoothConjugateInversePower_hasFDerivAt {distance : ℝ} (positive : 0 < distance)
    (power : ℕ) {position : ℂ} (separated : distance ≤ ‖position‖) :
    HasFDerivAt (smoothConjugateInversePower distance (power + 1))
      ((-((power + 1 : ℕ) : ℂ) * (star position)⁻¹ ^ (power + 2)) •
        (Complex.conjCLE : ℂ →L[ℝ] ℂ)) position := by
  have nonzero : position ≠ 0 := norm_pos_iff.mp (positive.trans_le separated)
  have raw := conjugate_zpow_hasFDerivAt (-((power + 1 : ℕ) : ℤ)) nonzero
  have exponent : -((power + 1 : ℕ) : ℤ) - 1 = -((power + 2 : ℕ) : ℤ) := by omega
  simp only [exponent, Int.cast_neg, Int.cast_natCast, zpow_neg, zpow_natCast, inv_pow] at raw
  simpa only [inv_pow] using raw.congr_of_eventuallyEq
    (show smoothConjugateInversePower distance (power + 1) =ᶠ[𝓝 position]
      (fun current => (star current ^ (power + 1))⁻¹) by
        simpa only [inv_pow] using smoothConjugateInversePower_eventuallyEq positive (power + 1) separated)

end EulerNonuniqueness.Section6
