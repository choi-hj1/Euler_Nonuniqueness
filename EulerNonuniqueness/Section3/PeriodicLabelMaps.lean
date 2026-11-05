import EulerNonuniqueness.Section3.PeriodicLabelShift
import EulerNonuniqueness.Section3.HolderLabelComposition

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem periodicLabelSlope_holder_bound (angular : PeriodicC1HolderHalf) (first second : ℝ) :
    |periodicLabelSlope angular first - periodicLabelSlope angular second| ≤ ‖angular‖ * Real.sqrt |first - second| := by
  have difference : periodicLabelSlope angular first - periodicLabelSlope angular second =
      (angular.val.2.val.1 first - angular.val.2.val.1 second).re := by
    dsimp only [periodicLabelSlope]
    rw [Complex.sub_re]
    ring
  rw [difference]
  exact (Complex.abs_re_le_norm _).trans (PeriodicC1HolderHalf.derivative_holder_bound angular first second)

def periodicForwardLabelMap (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2) : PeriodicC1LabelMap where
  map := periodicLabelShift angular
  slope := periodicLabelSlope angular
  bound := 2
  holder := ‖angular‖
  bound_nonnegative := by norm_num
  holder_nonnegative := norm_nonneg _
  continuous := periodicLabelShift_continuous angular
  slope_continuous := periodicLabelSlope_continuous angular
  hasDerivAt := periodicLabelShift_hasDerivAt angular
  add_period := periodicLabelShift_add_period angular
  slope_periodic := periodicLabelSlope_periodic angular
  slope_bound := fun label => (periodicLabelSlope_upper angular label).trans (by linarith)
  lipschitz_bound := fun first second => (periodicLabelShift_lipschitz_bound angular first second).trans
    (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
  holder_bound := periodicLabelSlope_holder_bound angular

def periodicInverseLabelSlope (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2) (label : ℝ) : ℝ :=
  (periodicLabelSlope angular ((periodicLabelHomeomorph angular (small.trans (by norm_num))).symm label))⁻¹

theorem periodicInverseLabelSlope_bound (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2) (label : ℝ) :
    |periodicInverseLabelSlope angular small label| ≤ 2 := by
  have lower := periodicLabelSlope_lower angular ((periodicLabelHomeomorph angular (small.trans (by norm_num))).symm label)
  have positive : 0 < periodicLabelSlope angular ((periodicLabelHomeomorph angular (small.trans (by norm_num))).symm label) := by linarith
  unfold periodicInverseLabelSlope
  rw [abs_of_pos (inv_pos.mpr positive)]
  rw [inv_eq_one_div]
  apply (div_le_iff₀ positive).mpr
  linarith

theorem abs_inverse_difference_le_four {first second : ℝ} (firstLower : 1 / 2 ≤ first) (secondLower : 1 / 2 ≤ second) :
    |first⁻¹ - second⁻¹| ≤ 4 * |first - second| := by
  have firstPositive : 0 < first := by linarith
  have secondPositive : 0 < second := by linarith
  have firstInverse : |first⁻¹| ≤ 2 := by
    rw [abs_of_pos (inv_pos.mpr firstPositive)]
    rw [inv_eq_one_div]
    exact (div_le_iff₀ firstPositive).mpr (by linarith)
  have secondInverse : |second⁻¹| ≤ 2 := by
    rw [abs_of_pos (inv_pos.mpr secondPositive)]
    rw [inv_eq_one_div]
    exact (div_le_iff₀ secondPositive).mpr (by linarith)
  have difference : first⁻¹ - second⁻¹ = first⁻¹ * (second - first) * second⁻¹ := by
    field_simp
    <;> ring
  rw [difference, abs_mul, abs_mul, abs_sub_comm second first]
  calc
    _ ≤ (2 * |first - second|) * 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right firstInverse (abs_nonneg _)) secondInverse
        (abs_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))
    _ = _ := by ring

theorem periodicInverseLabelSlope_holder_bound (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (first second : ℝ) :
    |periodicInverseLabelSlope angular small first - periodicInverseLabelSlope angular small second| ≤
      (8 * ‖angular‖) * Real.sqrt |first - second| := by
  let homeomorph := periodicLabelHomeomorph angular (small.trans (by norm_num))
  have lower (label : ℝ) : 1 / 2 ≤ periodicLabelSlope angular (homeomorph.symm label) :=
    (by linarith : 1 / 2 ≤ 1 - ‖angular‖).trans (periodicLabelSlope_lower angular _)
  have difference := abs_inverse_difference_le_four (lower first) (lower second)
  have slope := periodicLabelSlope_holder_bound angular (homeomorph.symm first) (homeomorph.symm second)
  have root : Real.sqrt |homeomorph.symm first - homeomorph.symm second| ≤ 2 * Real.sqrt |first - second| := by
    have close := periodicLabelHomeomorph_symm_lipschitz_bound angular small first second
    have estimate := Real.sqrt_le_sqrt close
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at estimate
    have two : Real.sqrt (2 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    exact estimate.trans (mul_le_mul_of_nonneg_right two (Real.sqrt_nonneg _))
  change |(periodicLabelSlope angular (homeomorph.symm first))⁻¹ -
      (periodicLabelSlope angular (homeomorph.symm second))⁻¹| ≤ _
  exact difference.trans ((mul_le_mul_of_nonneg_left (slope.trans
    (mul_le_mul_of_nonneg_left root (norm_nonneg angular))) (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring))

def periodicInverseLabelMap (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2) : PeriodicC1LabelMap where
  map := (periodicLabelHomeomorph angular (small.trans (by norm_num))).symm
  slope := periodicInverseLabelSlope angular small
  bound := 2
  holder := 8 * ‖angular‖
  bound_nonnegative := by norm_num
  holder_nonnegative := mul_nonneg (by norm_num) (norm_nonneg _)
  continuous := (periodicLabelHomeomorph angular (small.trans (by norm_num))).symm.continuous
  slope_continuous := by
    apply ((periodicLabelSlope_continuous angular).comp
      (periodicLabelHomeomorph angular (small.trans (by norm_num))).symm.continuous).inv₀
    intro label
    have lower := periodicLabelSlope_lower angular ((periodicLabelHomeomorph angular (small.trans (by norm_num))).symm label)
    exact (by linarith : 0 < periodicLabelSlope angular ((periodicLabelHomeomorph angular (small.trans (by norm_num))).symm label)).ne'
  hasDerivAt := periodicLabelHomeomorph_symm_hasDerivAt angular (small.trans (by norm_num))
  add_period := periodicLabelHomeomorph_symm_add_period angular (small.trans (by norm_num))
  slope_periodic := by
    intro label
    unfold periodicInverseLabelSlope
    rw [periodicLabelHomeomorph_symm_add_period, periodicLabelSlope_periodic]
  slope_bound := periodicInverseLabelSlope_bound angular small
  lipschitz_bound := periodicLabelHomeomorph_symm_lipschitz_bound angular small
  holder_bound := periodicInverseLabelSlope_holder_bound angular small

end EulerNonuniqueness.Paper
