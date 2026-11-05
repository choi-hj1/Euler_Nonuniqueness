import EulerNonuniqueness.General.WeightedInversePowerTriplet
import EulerNonuniqueness.Section1.ExternalFieldScaleBounds
import EulerNonuniqueness.Section1.DyadicSeparation
import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

def Scales.multipoleInteractionKernel (scales : Scales) (hessian : ℝ) (receiver source : ℕ) : ℝ :=
  let receiverLocation := scales.location receiver
  let sourceLocation := scales.location source
  let distance := |receiverLocation - sourceLocation| / 8
  scales.circulation source * scales.length source ^ 2 *
    ((1 / (receiverLocation * distance ^ 3) + 1 / distance ^ 4 + receiverLocation / distance ^ 5) +
      sourceLocation⁻¹ * (1 / (receiverLocation * distance ^ 2) + 1 / distance ^ 3 + receiverLocation / distance ^ 4) +
      sourceLocation * (1 / (receiverLocation * distance ^ 4) + 1 / distance ^ 5 + receiverLocation / distance ^ 6) +
      hessian * sourceLocation * (1 / (receiverLocation * distance ^ 3) + 1 / distance ^ 4 + receiverLocation / distance ^ 5))

theorem Scales.multipoleInteractionKernel_nonnegative (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {hessian : ℝ} (hessianNonnegative : 0 ≤ hessian) (receiver source : ℕ) :
    0 ≤ scales.multipoleInteractionKernel hessian receiver source := by
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive source
  have receiverPositive := scales.location_pos receiver
  have sourcePositive := scales.location_pos source
  dsimp only [Scales.multipoleInteractionKernel]
  positivity

theorem Scales.multipoleInteractionKernel_weighted_le (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {hessian : ℝ} (hessianSmall : hessian ≤ 1) {receiver source : ℕ} (different : receiver ≠ source) :
    scales.multipoleInteractionKernel hessian receiver source *
        (scales.location receiver / scales.location source) ^ 4 ≤
      216360000 * (scales.circulation source * scales.length source ^ 2 / scales.location source ^ 5) := by
  have distancePositive := div_pos (scales.location_distance_pos different) (show (0 : ℝ) < 8 by norm_num)
  have locations := scales.location_sum_le_three_distance different
  have receiverSeparated : scales.location receiver ≤ 24 * (|scales.location receiver - scales.location source| / 8) := by
    linarith [scales.location_pos source]
  have sourceSeparated : scales.location source ≤ 24 * (|scales.location receiver - scales.location source| / 8) := by
    linarith [scales.location_pos receiver]
  have estimate := EulerNonuniqueness.General.weighted_inverse_power_triplet_bound
    (scales.location_pos receiver) (scales.location_pos source) distancePositive
    (scales.location_le_one receiver) (scales.location_le_one source)
    (show (0 : ℝ) ≤ 24 by norm_num) receiverSeparated sourceSeparated hessianSmall
  norm_num only at estimate
  have prefactorNonnegative : 0 ≤ scales.circulation source * scales.length source ^ 2 :=
    mul_nonneg (scales.circulation_pos frequencyPositive ratioPositive source).le (sq_nonneg _)
  convert mul_le_mul_of_nonneg_left estimate prefactorNonnegative using 1 <;>
    dsimp only [Scales.multipoleInteractionKernel] <;> ring

theorem Scales.circulation_length_sq_location_summable (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (order : ℕ) :
    Summable (fun index : ℕ => scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
      scales.location (index + 1) ^ order) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  apply Summable.of_nonneg_of_le (fun index => by
    exact div_nonneg (mul_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
      (pow_nonneg (scales.location_pos _).le _)) _
    (scales.circulation_location_summable frequencyBound ratioBound alphaPositive order)
  intro index
  have lengthBound := scales.length_le_one frequencyPositive ratioPositive (index + 1)
  have lengthNonnegative := (scales.length_pos (index + 1)).le
  have lengthSquared : scales.length (index + 1) ^ 2 ≤ 1 := by nlinarith
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_right (scales.circulation_pos frequencyPositive ratioPositive _).le lengthSquared)
    (pow_nonneg (scales.location_pos _).le _)

theorem Scales.multipoleInteractionKernel_row_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {hessian : ℝ} (hessianSmall : hessian ≤ 1) (receiver : Fin count) :
    (∑ source ∈ Finset.univ.erase receiver,
      scales.multipoleInteractionKernel hessian (receiver.val + 1) (source.val + 1) *
        (scales.location (receiver.val + 1) / scales.location (source.val + 1)) ^ 4) ≤
      216360000 * ∑' source : ℕ,
        scales.circulation (source + 1) * scales.length (source + 1) ^ 2 / scales.location (source + 1) ^ 5 := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have first := Finset.sum_le_sum (fun source (member : source ∈ Finset.univ.erase receiver) =>
    scales.multipoleInteractionKernel_weighted_le frequencyPositive ratioPositive hessianSmall
      (show receiver.val + 1 ≠ source.val + 1 from fun same =>
        (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel same)).symm))
  apply first.trans
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 216360000)
  have finiteBound : (∑ source ∈ Finset.univ.erase receiver,
      scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2 / scales.location (source.val + 1) ^ 5) ≤
      ∑ source : Fin count,
        scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2 / scales.location (source.val + 1) ^ 5 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun source _ _ => by
      exact div_nonneg (mul_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
        (pow_nonneg (scales.location_pos _).le _))
  apply finiteBound.trans
  rw [Fin.sum_univ_eq_sum_range (fun source : ℕ =>
    scales.circulation (source + 1) * scales.length (source + 1) ^ 2 / scales.location (source + 1) ^ 5) count]
  exact (scales.circulation_length_sq_location_summable frequencyBound ratioBound alphaPositive 5).sum_le_tsum
    (Finset.range count) (fun source _ => by
      exact div_nonneg (mul_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
        (pow_nonneg (scales.location_pos _).le _))

theorem Scales.multipoleInteraction_total_tendsto_zero (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) :
    Tendsto (fun frequency : ℝ => 216360000 * ∑' source : ℕ,
      ({scales with frequency := frequency} : Scales).circulation (source + 1) *
        ({scales with frequency := frequency} : Scales).length (source + 1) ^ 2 /
          scales.location (source + 1) ^ 5) atTop (𝓝 0) := by
  have upper := (scales.circulation_location_total_tendsto_zero ratioBound alphaPositive 5).const_mul (216360000 : ℝ)
  simp only [mul_zero] at upper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds upper
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with frequency frequencyPositive
    apply mul_nonneg (by norm_num)
    apply tsum_nonneg
    intro source
    have circulationPositive := Scales.circulation_pos {scales with frequency := frequency}
      frequencyPositive (by change 0 < scales.ratio; linarith) (source + 1)
    exact div_nonneg (mul_nonneg circulationPositive.le (sq_nonneg _))
      (pow_nonneg (scales.location_pos _).le _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with frequency frequencyBound
    let changed : Scales := {scales with frequency := frequency}
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 216360000)
    apply Summable.tsum_le_tsum _
      (changed.circulation_length_sq_location_summable frequencyBound ratioBound alphaPositive 5)
      (changed.circulation_location_summable frequencyBound ratioBound alphaPositive 5)
    intro source
    have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
    have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
    have lengthBound := changed.length_le_one frequencyPositive ratioPositive (source + 1)
    have lengthNonnegative := (changed.length_pos (source + 1)).le
    have squared : changed.length (source + 1) ^ 2 ≤ 1 := by nlinarith
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (changed.circulation_pos frequencyPositive ratioPositive _).le squared)
      (pow_nonneg (changed.location_pos _).le _)

theorem Scales.multipoleInteraction_weighted_action_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {hessian envelope : ℝ} (hessianNonnegative : 0 ≤ hessian) (hessianSmall : hessian ≤ 1)
    (envelopeNonnegative : 0 ≤ envelope) (states : Fin count → ℝ)
    (statesBound : ∀ source, scales.location (source.val + 1) ^ 4 * states source ≤ envelope)
    (receiver : Fin count) :
    scales.location (receiver.val + 1) ^ 4 *
        (∑ source ∈ Finset.univ.erase receiver,
          scales.multipoleInteractionKernel hessian (receiver.val + 1) (source.val + 1) * states source) ≤
      (216360000 * ∑' source : ℕ,
        scales.circulation (source + 1) * scales.length (source + 1) ^ 2 / scales.location (source + 1) ^ 5) * envelope := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  rw [Finset.mul_sum]
  have individual (source : Fin count) :
      scales.location (receiver.val + 1) ^ 4 *
          (scales.multipoleInteractionKernel hessian (receiver.val + 1) (source.val + 1) * states source) ≤
      (scales.multipoleInteractionKernel hessian (receiver.val + 1) (source.val + 1) *
        (scales.location (receiver.val + 1) / scales.location (source.val + 1)) ^ 4) * envelope := by
    have coefficientNonnegative : 0 ≤ scales.multipoleInteractionKernel hessian
        (receiver.val + 1) (source.val + 1) *
          (scales.location (receiver.val + 1) / scales.location (source.val + 1)) ^ 4 :=
      mul_nonneg (scales.multipoleInteractionKernel_nonnegative frequencyPositive ratioPositive hessianNonnegative _ _)
        (pow_nonneg (div_nonneg (scales.location_pos _).le (scales.location_pos _).le) _)
    apply le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (statesBound source) coefficientNonnegative)
    field_simp [(scales.location_pos (source.val + 1)).ne']
    <;> ring
  apply (Finset.sum_le_sum (fun source _ => individual source)).trans
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (scales.multipoleInteractionKernel_row_le frequencyBound ratioBound alphaPositive hessianSmall receiver)
    envelopeNonnegative

end EulerNonuniqueness.Paper
