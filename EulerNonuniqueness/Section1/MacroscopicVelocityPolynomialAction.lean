import EulerNonuniqueness.Section1.MacroscopicCoefficientAction

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 8000000

def Scales.macroVelocityFeedbackPolynomial (scales : Scales) (constant : ℝ)
    (receiver source : ℕ) (receiverState sourceState : ℝ) : ℝ :=
  let receiverScale := scales.location receiver
  let sourceScale := scales.location source
  let distance := |receiverScale - sourceScale| / 8
  scales.circulation source * (4 * sourceScale / (receiverScale * distance ^ 2) +
    (16 + 384 * constant) * sourceScale ^ 2 / (receiverScale * distance ^ 3) +
    72 * sourceScale ^ 3 / (receiverScale * distance ^ 4)) * sourceState +
  scales.circulation source * (8 * sourceScale / distance ^ 3 + 72 * sourceScale ^ 2 / distance ^ 4) * receiverState

theorem Scales.macroVelocityFeedbackPolynomial_le (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {hessian constant receiverState sourceState : ℝ}
    (hessianNonnegative : 0 ≤ hessian) (constantNonnegative : 0 ≤ constant)
    (receiverStateNonnegative : 0 ≤ receiverState) (sourceStateNonnegative : 0 ≤ sourceState)
    {receiver source : ℕ} (different : receiver ≠ source) :
    scales.macroVelocityFeedbackPolynomial constant receiver source receiverState sourceState ≤
      (50000 * (constant + 1)) *
        (scales.macroscopicMultipoleInteractionKernel hessian receiver source * sourceState +
          scales.circulation source / (|scales.location receiver - scales.location source| / 8) ^ 2 * receiverState) := by
  let receiverScale := scales.location receiver
  let sourceScale := scales.location source
  let distance := |receiverScale - sourceScale| / 8
  have receiverPositive : 0 < receiverScale := scales.location_pos receiver
  have sourcePositive : 0 < sourceScale := scales.location_pos source
  have distancePositive : 0 < distance := div_pos (scales.location_distance_pos different) (by norm_num)
  have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive source).le
  have sourceScalar : 4 * sourceScale / (receiverScale * distance ^ 2) +
      (16 + 384 * constant) * sourceScale ^ 2 / (receiverScale * distance ^ 3) +
      72 * sourceScale ^ 3 / (receiverScale * distance ^ 4) ≤
      (500 * (constant + 1)) * (sourceScale / (receiverScale * distance ^ 2) +
        sourceScale ^ 2 / (receiverScale * distance ^ 3) + sourceScale ^ 3 / (receiverScale * distance ^ 4)) := by
    have generic (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
        4 * x + (16 + 384 * constant) * y + 72 * z ≤ 500 * (constant + 1) * (x + y + z) := by
      nlinarith [mul_nonneg constantNonnegative hx, mul_nonneg constantNonnegative hy, mul_nonneg constantNonnegative hz]
    convert generic (sourceScale / (receiverScale * distance ^ 2))
      (sourceScale ^ 2 / (receiverScale * distance ^ 3)) (sourceScale ^ 3 / (receiverScale * distance ^ 4))
      (by positivity) (by positivity) (by positivity) using 1 <;> ring
  have sourceBound := (mul_le_mul_of_nonneg_left sourceScalar circulationNonnegative).trans
    (by
      have actual := mul_le_mul_of_nonneg_left
        (scales.macroscopicMultipoleInteractionKernel_velocity_lower_bound frequencyPositive ratioPositive hessianNonnegative different)
        (show 0 ≤ 500 * (constant + 1) by positivity)
      convert actual using 1 <;> dsimp only [receiverScale, sourceScale, distance] <;> ring)
  have receiverScalar : 8 * sourceScale / distance ^ 3 + 72 * sourceScale ^ 2 / distance ^ 4 ≤
      3 * (8 * sourceScale / distance ^ 3 + 24 * sourceScale ^ 2 / distance ^ 4) := by
    have generic (x y : ℝ) (hx : 0 ≤ x) : 8 * x + 72 * y ≤ 3 * (8 * x + 24 * y) := by linarith
    convert generic (sourceScale / distance ^ 3) (sourceScale ^ 2 / distance ^ 4) (by positivity) using 1 <;> ring
  have receiverBound := (mul_le_mul_of_nonneg_left receiverScalar circulationNonnegative).trans
    (by
      have actual := mul_le_mul_of_nonneg_left
        (scales.multipoleVelocity_receiver_coefficient_bound frequencyPositive ratioPositive different) (by norm_num : (0 : ℝ) ≤ 3)
      convert actual using 1 <;> dsimp only [sourceScale, receiverScale, distance] <;> ring)
  have kernelNonnegative := scales.macroscopicMultipoleInteractionKernel_nonnegative frequencyPositive ratioPositive hessianNonnegative receiver source
  have sourceEnlarge := mul_le_mul_of_nonneg_right
    (show 500 * (constant + 1) ≤ 50000 * (constant + 1) by nlinarith) kernelNonnegative
  have receiverEnlarge := mul_le_mul_of_nonneg_right
    (show (42048 : ℝ) ≤ 50000 * (constant + 1) by nlinarith)
    (div_nonneg circulationNonnegative (sq_nonneg distance))
  have first := mul_le_mul_of_nonneg_right (sourceBound.trans sourceEnlarge) sourceStateNonnegative
  have second := mul_le_mul_of_nonneg_right (receiverBound.trans (by convert receiverEnlarge using 1 <;> ring)) receiverStateNonnegative
  convert add_le_add first second using 1 <;> dsimp only [Scales.macroVelocityFeedbackPolynomial, receiverScale, sourceScale, distance] <;> ring

theorem Scales.macroVelocityFeedbackPolynomial_weighted_action_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {hessian constant : ℝ} (hessianNonnegative : 0 ≤ hessian) (hessianSmall : hessian ≤ 1)
    (constantNonnegative : 0 ≤ constant)
    (states : Fin count → ℝ) (statesNonnegative : ∀ source, 0 ≤ states source)
    (receiver : Fin count) (selected : Finset (Fin count)) (selectedSubset : selected ⊆ Finset.univ.erase receiver) :
    scales.location (receiver.val + 1) ^ 4 * (∑ source ∈ selected,
      scales.macroVelocityFeedbackPolynomial constant (receiver.val + 1) (source.val + 1) (states receiver) (states source)) ≤
      (50000 * (constant + 1)) * (216360000 * scales.hessian + 576 * scales.strain) *
        ‖fun source : Fin count => scales.location (source.val + 1) ^ 4 * states source‖ := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have individual (source : Fin count) (member : source ∈ selected) :=
    scales.macroVelocityFeedbackPolynomial_le frequencyPositive ratioPositive hessianNonnegative constantNonnegative
      (statesNonnegative receiver) (statesNonnegative source)
      (show receiver.val + 1 ≠ source.val + 1 from fun equality =>
        (Finset.mem_erase.mp (selectedSubset member)).1 (Fin.ext (Nat.add_right_cancel equality)).symm)
  have finiteBound := Finset.sum_le_sum individual
  have weighted := mul_le_mul_of_nonneg_left finiteBound (pow_nonneg (scales.location_pos (receiver.val + 1)).le 4)
  have row := mul_le_mul_of_nonneg_left
    (scales.macroscopic_feedback_weighted_action_le frequencyBound ratioBound alphaPositive hessianNonnegative hessianSmall
      states statesNonnegative receiver selected selectedSubset) (show 0 ≤ 50000 * (constant + 1) by positivity)
  apply weighted.trans
  convert row using 1
  · rw [← Finset.mul_sum]
    ring
  · ring

end EulerNonuniqueness.Paper
