import EulerNonuniqueness.Section1.MultipoleInteractionRow

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

def Scales.macroscopicMultipoleInteractionKernel (scales : Scales) (hessian : ℝ) (receiver source : ℕ) : ℝ :=
  (scales.location source ^ 2 / scales.length source ^ 2) *
    scales.multipoleInteractionKernel hessian receiver source

theorem Scales.macroscopicMultipoleInteractionKernel_nonnegative (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {hessian : ℝ} (hessianNonnegative : 0 ≤ hessian) (receiver source : ℕ) :
    0 ≤ scales.macroscopicMultipoleInteractionKernel hessian receiver source :=
  mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
    (scales.multipoleInteractionKernel_nonnegative frequencyPositive ratioPositive hessianNonnegative receiver source)

theorem Scales.macroscopicMultipoleInteractionKernel_weighted_le (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {hessian : ℝ} (hessianSmall : hessian ≤ 1) {receiver source : ℕ} (different : receiver ≠ source) :
    scales.macroscopicMultipoleInteractionKernel hessian receiver source *
      (scales.location receiver / scales.location source) ^ 4 ≤
        216360000 * scales.circulation source / scales.location source ^ 3 := by
  have actual := mul_le_mul_of_nonneg_left
    (scales.multipoleInteractionKernel_weighted_le frequencyPositive ratioPositive hessianSmall different)
    (show 0 ≤ scales.location source ^ 2 / scales.length source ^ 2 by positivity)
  convert actual using 1
  · dsimp only [Scales.macroscopicMultipoleInteractionKernel]
    ring
  · field_simp [(scales.length_pos source).ne', (scales.location_pos source).ne']
    <;> ring

theorem Scales.macroscopicMultipoleInteractionKernel_row_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {hessian : ℝ} (hessianSmall : hessian ≤ 1) (receiver : Fin count) :
    (∑ source ∈ Finset.univ.erase receiver,
      scales.macroscopicMultipoleInteractionKernel hessian (receiver.val + 1) (source.val + 1) *
        (scales.location (receiver.val + 1) / scales.location (source.val + 1)) ^ 4) ≤
      216360000 * scales.hessian := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have first := Finset.sum_le_sum (fun source (member : source ∈ Finset.univ.erase receiver) =>
    scales.macroscopicMultipoleInteractionKernel_weighted_le frequencyPositive ratioPositive hessianSmall
      (show receiver.val + 1 ≠ source.val + 1 from fun equality =>
        (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality)).symm))
  apply first.trans
  have scalarIdentity : (∑ source ∈ Finset.univ.erase receiver,
      216360000 * scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 3) =
      216360000 * ∑ source ∈ Finset.univ.erase receiver,
        scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 3 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    ring
  rw [scalarIdentity]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 216360000)
  have finiteBound : (∑ source ∈ Finset.univ.erase receiver,
      scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 3) ≤
      ∑ source : Fin count, scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 3 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun source _ _ => by
      exact div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
        (pow_nonneg (scales.location_pos _).le _))
  apply finiteBound.trans
  rw [Fin.sum_univ_eq_sum_range (fun source : ℕ =>
    scales.circulation (source + 1) / scales.location (source + 1) ^ 3) count]
  exact (scales.circulation_location_summable frequencyBound ratioBound alphaPositive 3).sum_le_tsum
    (Finset.range count) (fun source _ => by
      exact div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
        (pow_nonneg (scales.location_pos _).le _))

theorem Scales.macroscopicMultipoleInteraction_weighted_action_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {hessian envelope : ℝ} (hessianNonnegative : 0 ≤ hessian) (hessianSmall : hessian ≤ 1)
    (envelopeNonnegative : 0 ≤ envelope) (states : Fin count → ℝ)
    (statesBound : ∀ source, scales.location (source.val + 1) ^ 4 * states source ≤ envelope)
    (receiver : Fin count) :
    scales.location (receiver.val + 1) ^ 4 *
      (∑ source ∈ Finset.univ.erase receiver,
        scales.macroscopicMultipoleInteractionKernel hessian (receiver.val + 1) (source.val + 1) * states source) ≤
      (216360000 * scales.hessian) * envelope := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  rw [Finset.mul_sum]
  have individual (source : Fin count) :
      scales.location (receiver.val + 1) ^ 4 *
        (scales.macroscopicMultipoleInteractionKernel hessian (receiver.val + 1) (source.val + 1) * states source) ≤
      (scales.macroscopicMultipoleInteractionKernel hessian (receiver.val + 1) (source.val + 1) *
        (scales.location (receiver.val + 1) / scales.location (source.val + 1)) ^ 4) * envelope := by
    have coefficientNonnegative : 0 ≤ scales.macroscopicMultipoleInteractionKernel hessian
        (receiver.val + 1) (source.val + 1) *
        (scales.location (receiver.val + 1) / scales.location (source.val + 1)) ^ 4 := by
      exact mul_nonneg
        (scales.macroscopicMultipoleInteractionKernel_nonnegative frequencyPositive ratioPositive hessianNonnegative _ _)
        (pow_nonneg (div_nonneg (scales.location_pos _).le (scales.location_pos _).le) _)
    apply le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (statesBound source) coefficientNonnegative)
    field_simp [(scales.location_pos (source.val + 1)).ne']
    <;> ring
  apply (Finset.sum_le_sum (fun source _ => individual source)).trans
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (scales.macroscopicMultipoleInteractionKernel_row_le frequencyBound ratioBound alphaPositive hessianSmall receiver)
    envelopeNonnegative

theorem Scales.eventually_macroscopicMultipoleInteraction_small (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ hessian : ℝ, hessian ≤ 1 → ∀ receiver : Fin count,
      (∑ source ∈ Finset.univ.erase receiver,
        ({scales with frequency := frequency} : Scales).macroscopicMultipoleInteractionKernel hessian
          (receiver.val + 1) (source.val + 1) *
          (scales.location (receiver.val + 1) / scales.location (source.val + 1)) ^ 4) < tolerance := by
  have small := ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul (216360000 : ℝ)).eventually
    (eventually_lt_nhds (by simpa only [mul_zero] using tolerancePositive))
  filter_upwards [eventually_ge_atTop (1 : ℝ), small] with frequency frequencyBound small
  intro count hessian hessianSmall receiver
  exact (({scales with frequency := frequency} : Scales).macroscopicMultipoleInteractionKernel_row_le
    frequencyBound ratioBound alphaPositive hessianSmall receiver).trans_lt small

theorem Scales.macroscopicMultipoleInteractionKernel_velocity_lower_bound (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {hessian : ℝ} (hessianNonnegative : 0 ≤ hessian) {receiver source : ℕ} (different : receiver ≠ source) :
    let receiverScale := scales.location receiver
    let sourceScale := scales.location source
    let distance := |receiverScale - sourceScale| / 8
    scales.circulation source *
      (sourceScale / (receiverScale * distance ^ 2) +
        sourceScale ^ 2 / (receiverScale * distance ^ 3) +
        sourceScale ^ 3 / (receiverScale * distance ^ 4)) ≤
      scales.macroscopicMultipoleInteractionKernel hessian receiver source := by
  dsimp only
  let receiverScale := scales.location receiver
  let sourceScale := scales.location source
  let distance := |receiverScale - sourceScale| / 8
  have receiverPositive : 0 < receiverScale := scales.location_pos receiver
  have sourcePositive : 0 < sourceScale := scales.location_pos source
  have distancePositive : 0 < distance := div_pos (scales.location_distance_pos different) (by norm_num)
  have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive source).le
  have identity : scales.macroscopicMultipoleInteractionKernel hessian receiver source =
      scales.circulation source *
        (sourceScale / (receiverScale * distance ^ 2) +
          sourceScale ^ 2 / (receiverScale * distance ^ 3) +
          sourceScale ^ 3 / (receiverScale * distance ^ 4)) +
      scales.circulation source *
        (sourceScale ^ 2 * (1 / distance ^ 4 + receiverScale / distance ^ 5) +
          sourceScale * (1 / distance ^ 3 + receiverScale / distance ^ 4) +
          sourceScale ^ 3 * (1 / distance ^ 5 + receiverScale / distance ^ 6) +
          hessian * sourceScale ^ 3 *
            (1 / (receiverScale * distance ^ 3) + 1 / distance ^ 4 + receiverScale / distance ^ 5)) := by
    dsimp only [Scales.macroscopicMultipoleInteractionKernel, Scales.multipoleInteractionKernel]
    change (sourceScale ^ 2 / scales.length source ^ 2) *
      (scales.circulation source * scales.length source ^ 2 *
        ((1 / (receiverScale * distance ^ 3) + 1 / distance ^ 4 + receiverScale / distance ^ 5) +
          sourceScale⁻¹ *
            (1 / (receiverScale * distance ^ 2) + 1 / distance ^ 3 + receiverScale / distance ^ 4) +
          sourceScale *
            (1 / (receiverScale * distance ^ 4) + 1 / distance ^ 5 + receiverScale / distance ^ 6) +
          hessian * sourceScale *
            (1 / (receiverScale * distance ^ 3) + 1 / distance ^ 4 + receiverScale / distance ^ 5))) = _
    field_simp [receiverPositive.ne', sourcePositive.ne', distancePositive.ne', (scales.length_pos source).ne']
    <;> ring
  rw [identity]
  exact le_add_of_nonneg_right (by positivity)

theorem Scales.multipoleVelocity_receiver_coefficient_bound (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {receiver source : ℕ} (different : receiver ≠ source) :
    let sourceScale := scales.location source
    let distance := |scales.location receiver - sourceScale| / 8
    scales.circulation source * (8 * sourceScale / distance ^ 3 + 24 * sourceScale ^ 2 / distance ^ 4) ≤
      14016 * scales.circulation source / distance ^ 2 := by
  dsimp only
  let sourceScale := scales.location source
  let distance := |scales.location receiver - sourceScale| / 8
  change scales.circulation source *
    (8 * sourceScale / distance ^ 3 + 24 * sourceScale ^ 2 / distance ^ 4) ≤
      14016 * scales.circulation source / distance ^ 2
  have sourcePositive : 0 < sourceScale := scales.location_pos source
  have distancePositive : 0 < distance := div_pos (scales.location_distance_pos different) (by norm_num)
  have geometry := scales.location_sum_le_three_distance different
  have sourceBound : sourceScale ≤ 24 * distance := by
    dsimp only [sourceScale, distance]
    linarith [scales.location_pos receiver]
  have ratioNonnegative : 0 ≤ sourceScale / distance := by positivity
  have ratioBound : sourceScale / distance ≤ 24 := (div_le_iff₀ distancePositive).mpr sourceBound
  have scalar : 8 * (sourceScale / distance) + 24 * (sourceScale / distance) ^ 2 ≤ 14016 := by
    have squareBound := pow_le_pow_left₀ ratioNonnegative ratioBound 2
    nlinarith
  have actual := mul_le_mul_of_nonneg_left scalar
    (show 0 ≤ scales.circulation source / distance ^ 2 from
      div_nonneg (scales.circulation_pos frequencyPositive ratioPositive source).le (sq_nonneg _))
  convert actual using 1 <;> field_simp <;> ring

end EulerNonuniqueness.Paper
