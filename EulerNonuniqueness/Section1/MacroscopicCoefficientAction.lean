import EulerNonuniqueness.Section1.MacroscopicCoefficientEnvelopeRow
import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 8000000

theorem Scales.coefficient_source_polynomial_bound (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {hessian constant : ℝ} (hessianNonnegative : 0 ≤ hessian) (constantNonnegative : 0 ≤ constant)
    {receiver source : ℕ} (different : receiver ≠ source) :
    let sourceScale := scales.location source
    let distance := |scales.location receiver - sourceScale| / 8
    scales.circulation source * (32 * sourceScale / distance ^ 3 +
      (512 + 73728 * constant) * sourceScale ^ 2 / distance ^ 4 + 12288 * sourceScale ^ 3 / distance ^ 5) ≤
      (2160000 * (constant + 1)) * scales.macroscopicMultipoleInteractionKernel hessian receiver source := by
  dsimp only
  let sourceScale := scales.location source
  let distance := |scales.location receiver - sourceScale| / 8
  have sourcePositive : 0 < sourceScale := scales.location_pos source
  have distancePositive : 0 < distance := div_pos (scales.location_distance_pos different) (by norm_num)
  have scalar : 32 * sourceScale / distance ^ 3 +
      (512 + 73728 * constant) * sourceScale ^ 2 / distance ^ 4 + 12288 * sourceScale ^ 3 / distance ^ 5 ≤
      (90000 * (constant + 1)) * (sourceScale / distance ^ 3 + sourceScale ^ 2 / distance ^ 4 + sourceScale ^ 3 / distance ^ 5) := by
    have first : 0 ≤ sourceScale / distance ^ 3 := by positivity
    have second : 0 ≤ sourceScale ^ 2 / distance ^ 4 := by positivity
    have third : 0 ≤ sourceScale ^ 3 / distance ^ 5 := by positivity
    have generic (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
        32 * x + (512 + 73728 * constant) * y + 12288 * z ≤
          (90000 * (constant + 1)) * (x + y + z) := by
      nlinarith [mul_nonneg constantNonnegative hx, mul_nonneg constantNonnegative hy, mul_nonneg constantNonnegative hz]
    convert generic _ _ _ first second third using 1 <;> ring
  have weighted := mul_le_mul_of_nonneg_left scalar (scales.circulation_pos frequencyPositive ratioPositive source).le
  have row := mul_le_mul_of_nonneg_left
    (scales.macroscopicMultipoleInteractionKernel_coefficient_lower_bound frequencyPositive ratioPositive hessianNonnegative different)
    (show 0 ≤ 90000 * (constant + 1) by positivity)
  change scales.circulation source * _ ≤ _
  apply weighted.trans
  convert row using 1 <;> dsimp only [sourceScale, distance] <;> ring

theorem Scales.coefficient_receiver_polynomial_bound (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {receiver source : ℕ} (different : receiver ≠ source) :
    let receiverScale := scales.location receiver
    let sourceScale := scales.location source
    let distance := |receiverScale - sourceScale| / 8
    scales.circulation source * (256 * receiverScale * sourceScale / distance ^ 4 +
      12288 * receiverScale * sourceScale ^ 2 / distance ^ 5) ≤
      180000000 * scales.circulation source / distance ^ 2 := by
  dsimp only
  let receiverScale := scales.location receiver
  let sourceScale := scales.location source
  let distance := |receiverScale - sourceScale| / 8
  have receiverPositive : 0 < receiverScale := scales.location_pos receiver
  have sourcePositive : 0 < sourceScale := scales.location_pos source
  have distancePositive : 0 < distance := div_pos (scales.location_distance_pos different) (by norm_num)
  have scalar : 256 * receiverScale * sourceScale / distance ^ 4 +
      12288 * receiverScale * sourceScale ^ 2 / distance ^ 5 ≤
      3 * (256 * receiverScale * sourceScale / distance ^ 4 + 4096 * receiverScale * sourceScale ^ 2 / distance ^ 5) := by
    have positive : 0 ≤ receiverScale * sourceScale / distance ^ 4 := by positivity
    have generic (x y : ℝ) (nonnegative : 0 ≤ x) : 256 * x + 12288 * y ≤ 3 * (256 * x + 4096 * y) := by linarith
    convert generic _ (receiverScale * sourceScale ^ 2 / distance ^ 5) positive using 1 <;> ring
  have weighted := mul_le_mul_of_nonneg_left scalar (scales.circulation_pos frequencyPositive ratioPositive source).le
  have row := mul_le_mul_of_nonneg_left
    (scales.coefficient_receiver_coarse_bound frequencyPositive ratioPositive different) (by norm_num : (0 : ℝ) ≤ 3)
  apply weighted.trans
  convert row using 1 <;> dsimp only [receiverScale, sourceScale, distance] <;> ring

theorem Scales.macroscopic_feedback_weighted_action_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {hessian : ℝ} (hessianNonnegative : 0 ≤ hessian) (hessianSmall : hessian ≤ 1)
    (states : Fin count → ℝ) (statesNonnegative : ∀ source, 0 ≤ states source)
    (receiver : Fin count) (selected : Finset (Fin count)) (selectedSubset : selected ⊆ Finset.univ.erase receiver) :
    scales.location (receiver.val + 1) ^ 4 * (∑ source ∈ selected,
      (scales.macroscopicMultipoleInteractionKernel hessian (receiver.val + 1) (source.val + 1) * states source +
        scales.circulation (source.val + 1) /
          (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ 2 * states receiver)) ≤
      (216360000 * scales.hessian + 576 * scales.strain) *
        ‖fun source : Fin count => scales.location (source.val + 1) ^ 4 * states source‖ := by
  let envelope := ‖fun source : Fin count => scales.location (source.val + 1) ^ 4 * states source‖
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive (source + 1)).le (sq_nonneg _)
  have stateBound (source : Fin count) : scales.location (source.val + 1) ^ 4 * states source ≤ envelope := by
    exact (le_abs_self _).trans (norm_le_pi_norm (fun source : Fin count => scales.location (source.val + 1) ^ 4 * states source) source)
  have enlarge : (∑ source ∈ selected,
      (scales.macroscopicMultipoleInteractionKernel hessian (receiver.val + 1) (source.val + 1) * states source +
        scales.circulation (source.val + 1) /
          (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ 2 * states receiver)) ≤
      ∑ source ∈ Finset.univ.erase receiver,
      (scales.macroscopicMultipoleInteractionKernel hessian (receiver.val + 1) (source.val + 1) * states source +
        scales.circulation (source.val + 1) /
          (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ 2 * states receiver) :=
    Finset.sum_le_sum_of_subset_of_nonneg selectedSubset (fun source _ _ =>
    add_nonneg
      (mul_nonneg (scales.macroscopicMultipoleInteractionKernel_nonnegative frequencyPositive ratioPositive hessianNonnegative _ _) (statesNonnegative source))
      (mul_nonneg (div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)) (statesNonnegative receiver)))
  apply (mul_le_mul_of_nonneg_left enlarge (pow_nonneg (scales.location_pos _).le 4)).trans
  rw [Finset.sum_add_distrib, mul_add]
  have sourceBound := scales.macroscopicMultipoleInteraction_weighted_action_le frequencyBound ratioBound alphaPositive
    hessianNonnegative hessianSmall (norm_nonneg _) states stateBound receiver
  have receiverRow := scales.sum_foreignInteractionWeight_le frequencyBound ratioBound alphaPositive receiver 2
  norm_num only [show (24 : ℝ) ^ 2 = 576 by norm_num] at receiverRow
  change (∑ source ∈ Finset.univ.erase receiver, scales.circulation (source.val + 1) /
    (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ 2) ≤ 576 * scales.strain at receiverRow
  have receiverBound := mul_le_mul receiverRow (stateBound receiver)
    (mul_nonneg (pow_nonneg (scales.location_pos _).le 4) (statesNonnegative receiver))
    (by positivity : 0 ≤ 576 * scales.strain)
  have diagonal : scales.location (receiver.val + 1) ^ 4 *
      (∑ source ∈ Finset.univ.erase receiver, scales.circulation (source.val + 1) /
        (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ 2 * states receiver) ≤
      576 * scales.strain * envelope := by
    rw [← Finset.sum_mul]
    convert receiverBound using 1 <;> ring
  exact (add_le_add sourceBound diagonal).trans_eq (by ring)

end EulerNonuniqueness.Paper
