import EulerNonuniqueness.Section1.MacroscopicCoefficientAction

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 8000000

def Scales.macroCoefficientFeedbackPolynomial (scales : Scales) (constant weight : ℝ)
    (receiver source : ℕ) (receiverState sourceState : ℝ) : ℝ :=
  let receiverScale := scales.location receiver
  let sourceScale := scales.location source
  let distance := |receiverScale - sourceScale| / 8
  scales.circulation source * weight * (32 * sourceScale / distance ^ 3 +
    (512 + 73728 * constant) * sourceScale ^ 2 / distance ^ 4 + 12288 * sourceScale ^ 3 / distance ^ 5) * sourceState +
  scales.circulation source * weight * (256 * receiverScale * sourceScale / distance ^ 4 +
    12288 * receiverScale * sourceScale ^ 2 / distance ^ 5) * receiverState

theorem Scales.macroCoefficientFeedbackPolynomial_le (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {hessian constant weight receiverState sourceState : ℝ}
    (hessianNonnegative : 0 ≤ hessian) (constantNonnegative : 0 ≤ constant) (weightNonnegative : 0 ≤ weight)
    (receiverStateNonnegative : 0 ≤ receiverState) (sourceStateNonnegative : 0 ≤ sourceState)
    {receiver source : ℕ} (different : receiver ≠ source) :
    scales.macroCoefficientFeedbackPolynomial constant weight receiver source receiverState sourceState ≤
      (1000000000 * (constant + 1) * weight) *
        (scales.macroscopicMultipoleInteractionKernel hessian receiver source * sourceState +
          scales.circulation source / (|scales.location receiver - scales.location source| / 8) ^ 2 * receiverState) := by
  have sourceBound := mul_le_mul_of_nonneg_right
    (scales.coefficient_source_polynomial_bound frequencyPositive ratioPositive hessianNonnegative constantNonnegative different)
    (mul_nonneg weightNonnegative sourceStateNonnegative)
  have receiverBound := mul_le_mul_of_nonneg_right
    (scales.coefficient_receiver_polynomial_bound frequencyPositive ratioPositive different)
    (mul_nonneg weightNonnegative receiverStateNonnegative)
  have kernelNonnegative := scales.macroscopicMultipoleInteractionKernel_nonnegative frequencyPositive ratioPositive hessianNonnegative receiver source
  have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive source).le
  have sourceScalar : 2160000 * (constant + 1) ≤ 1000000000 * (constant + 1) := by nlinarith
  have receiverScalar : (180000000 : ℝ) ≤ 1000000000 * (constant + 1) := by nlinarith
  have sourceEnlarge := mul_le_mul_of_nonneg_right sourceScalar
    (mul_nonneg kernelNonnegative (mul_nonneg weightNonnegative sourceStateNonnegative))
  have receiverEnlarge := mul_le_mul_of_nonneg_right receiverScalar
    (mul_nonneg (div_nonneg circulationNonnegative
      (sq_nonneg (|scales.location receiver - scales.location source| / 8)))
      (mul_nonneg weightNonnegative receiverStateNonnegative))
  have first := sourceBound.trans (by convert sourceEnlarge using 1 <;> ring)
  have second := receiverBound.trans (by convert receiverEnlarge using 1 <;> ring)
  convert add_le_add first second using 1 <;> dsimp only [Scales.macroCoefficientFeedbackPolynomial] <;> ring

theorem Scales.macroCoefficientFeedbackPolynomial_weighted_action_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {hessian constant weight : ℝ} (hessianNonnegative : 0 ≤ hessian) (hessianSmall : hessian ≤ 1)
    (constantNonnegative : 0 ≤ constant) (weightNonnegative : 0 ≤ weight)
    (states : Fin count → ℝ) (statesNonnegative : ∀ source, 0 ≤ states source)
    (receiver : Fin count) (selected : Finset (Fin count)) (selectedSubset : selected ⊆ Finset.univ.erase receiver) :
    scales.location (receiver.val + 1) ^ 4 * (∑ source ∈ selected,
      scales.macroCoefficientFeedbackPolynomial constant weight (receiver.val + 1) (source.val + 1)
        (states receiver) (states source)) ≤
      (1000000000 * (constant + 1) * weight) * (216360000 * scales.hessian + 576 * scales.strain) *
        ‖fun source : Fin count => scales.location (source.val + 1) ^ 4 * states source‖ := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have individual (source : Fin count) (member : source ∈ selected) :=
    scales.macroCoefficientFeedbackPolynomial_le frequencyPositive ratioPositive hessianNonnegative constantNonnegative
      weightNonnegative (statesNonnegative receiver) (statesNonnegative source)
      (show receiver.val + 1 ≠ source.val + 1 from fun equality =>
        (Finset.mem_erase.mp (selectedSubset member)).1 (Fin.ext (Nat.add_right_cancel equality)).symm)
  have finiteBound := Finset.sum_le_sum individual
  have weighted := mul_le_mul_of_nonneg_left finiteBound (pow_nonneg (scales.location_pos (receiver.val + 1)).le 4)
  have row := mul_le_mul_of_nonneg_left
    (scales.macroscopic_feedback_weighted_action_le frequencyBound ratioBound alphaPositive hessianNonnegative hessianSmall
      states statesNonnegative receiver selected selectedSubset) (show 0 ≤ 1000000000 * (constant + 1) * weight by positivity)
  apply weighted.trans
  convert row using 1
  · rw [← Finset.mul_sum]
    ring
  · ring

end EulerNonuniqueness.Paper
