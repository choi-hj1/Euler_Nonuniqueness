import EulerNonuniqueness.Section5.CascadeMixedFollowerClosedWeightedForcing
import EulerNonuniqueness.Section5.CascadeMixedSelectedFinerOriginalPrefixBudget

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem CascadeSourcePreparedPair.mixed_common_sharp_budget_comparison
    {cap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
    {count : ℕ} (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold
      referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (receiver : Fin count) {incomingConstant outgoingConstant extent coefficient weight finish rho : ℝ}
    (entry initialDistance magnitude : Fin count → ℝ)
    (frequencyPositive : 0 < scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (incomingNonnegative : 0 ≤ incomingConstant) (outgoingNonnegative : 0 ≤ outgoingConstant)
    (coefficientPositive : 0 < coefficient) (weightPositive : 0 < weight) (rhoNonnegative : 0 ≤ rho)
    (magnitudeNonnegative : ∀ source : Fin count, receiver.val < source.val → 0 ≤ magnitude source)
    (distanceNonnegative : ∀ source : Fin count, receiver.val < source.val → 0 ≤ initialDistance source) :
    rho / (scales.omega (receiver.val + 1) * scales.location (receiver.val + 1) ^ 4) *
        prepared.mixedFollowerSourcePrefixBudget receiver incomingConstant outgoingConstant extent coefficient
          entry initialDistance magnitude weight finish ≤
      (rho / scales.frequency) *
        prepared.mixedSelectedFinerSourcePrefixBudget receiver incomingConstant outgoingConstant extent coefficient
          entry initialDistance magnitude weight finish := by
  classical
  let location := scales.location (receiver.val + 1)
  let finer := Finset.univ.filter (fun source : Fin count => receiver.val < source.val)
  let gap := fun source : Fin count => |location - scales.location (source.val + 1)|
  let common := fun source : Fin count =>
    scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2 *
      (1 + (scales.location (source.val + 1))⁻¹) * magnitude source /
      (coefficient * scales.omega (source.val + 1)) * Real.exp (-weight * entry source)
  let sharp := fun source : Fin count =>
    scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2 / gap source ^ 4 *
      (1 + location / scales.location (source.val + 1)) * magnitude source /
      (coefficient * scales.omega (source.val + 1)) * Real.exp (-weight * entry source)
  let later := fun source : Fin count =>
    scales.circulation (source.val + 1) * (scales.circulation (source.val + 1) / weight ^ 2 +
      ((1 + initialDistance source) * scales.length (source.val + 1) ^ 2 +
        ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion (entry source) source‖) / weight) *
      Real.exp (-weight * entry source)
  have locationPositive : 0 < location := scales.location_pos _
  have locationOne : location ≤ 1 := scales.location_le_one _
  have ratioPositive : 0 < scales.ratio := lt_of_lt_of_le (by norm_num) ratioBound
  have memberBelow (source : Fin count) (member : source ∈ finer) : receiver.val < source.val :=
    (Finset.mem_filter.mp member).2
  have gapPositive (source : Fin count) (member : source ∈ finer) : 0 < gap source :=
    scales.location_distance_pos (by have below := memberBelow source member; omega)
  have gapBound (source : Fin count) (member : source ∈ finer) : gap source ≤ location := by
    have ordered : receiver.val + 1 ≤ source.val + 1 := by have below := memberBelow source member; omega
    have smaller := scales.location_antitone ordered
    rw [show gap source = location - scales.location (source.val + 1) from abs_of_nonneg (sub_nonneg.mpr smaller)]
    exact sub_le_self _ (scales.location_pos _).le
  have incomingBound (source : Fin count) (member : source ∈ finer) : location * common source ≤ location ^ 4 * sharp source := by
    have sourcePositive := scales.location_pos (source.val + 1)
    have powerBound := pow_le_pow_left₀ (gapPositive source member).le (gapBound source member) 4
    have quotientOne : (1 : ℝ) ≤ location ^ 4 / gap source ^ 4 :=
      (le_div_iff₀ (pow_pos (gapPositive source member) 4)).mpr (by simpa only [one_mul] using powerBound)
    have factorBound : location * (1 + (scales.location (source.val + 1))⁻¹) ≤
        (location ^ 4 / gap source ^ 4) * (1 + location / scales.location (source.val + 1)) := by
      calc
        _ ≤ 1 + location / scales.location (source.val + 1) := by
          simpa only [mul_add, mul_one, div_eq_mul_inv] using
            add_le_add_right locationOne (location * (scales.location (source.val + 1))⁻¹)
        _ ≤ _ := le_mul_of_one_le_left (by positivity) quotientOne
    have baseNonnegative : 0 ≤ scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2 *
        magnitude source / (coefficient * scales.omega (source.val + 1)) * Real.exp (-weight * entry source) :=
      mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg
        (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
        (magnitudeNonnegative source (memberBelow source member)))
        (mul_pos coefficientPositive (scales.omega_pos frequencyPositive ratioPositive _)).le) (Real.exp_pos _).le
    have scaled := mul_le_mul_of_nonneg_left factorBound baseNonnegative
    convert scaled using 1 <;> dsimp only [common, sharp] <;> simp only [div_eq_mul_inv] <;> ring
  have sharpNonnegative (source : Fin count) (member : source ∈ finer) : 0 ≤ sharp source := by
    dsimp only [sharp]
    exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg
      (div_nonneg (mul_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
        (pow_nonneg (gapPositive source member).le 4))
      (add_nonneg zero_le_one (div_nonneg locationPositive.le (scales.location_pos _).le)))
      (magnitudeNonnegative source (memberBelow source member)))
      (mul_pos coefficientPositive (scales.omega_pos frequencyPositive ratioPositive _)).le) (Real.exp_pos _).le
  have laterNonnegative (source : Fin count) (member : source ∈ finer) : 0 ≤ later source := by
    have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (source.val + 1)
    have distanceBound := distanceNonnegative source (memberBelow source member)
    dsimp only [later]
    positivity
  have incomingSum : location * (∑ source ∈ finer, common source) ≤ location ^ 4 * (∑ source ∈ finer, sharp source) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_le_sum incomingBound
  have laterSumNonnegative : 0 ≤ ∑ source ∈ finer.filter (fun source => entry source < finish), later source :=
    Finset.sum_nonneg fun source member => laterNonnegative source (Finset.mem_filter.mp member).1
  have combined := add_le_add
    (mul_le_mul_of_nonneg_left incomingSum (mul_nonneg incomingNonnegative (sq_nonneg extent)))
    (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left laterSumNonnegative locationOne) outgoingNonnegative)
  have commonIdentity : location * prepared.mixedFollowerSourcePrefixBudget receiver incomingConstant outgoingConstant extent coefficient
      entry initialDistance magnitude weight finish =
      incomingConstant * extent ^ 2 * (location * ∑ source ∈ finer, common source) +
        outgoingConstant * (location * ∑ source ∈ finer.filter (fun source => entry source < finish), later source) := by
    change location * (incomingConstant * extent ^ 2 * (∑ source ∈ finer, common source) +
      outgoingConstant * (∑ source ∈ finer.filter (fun source => entry source < finish), later source)) = _
    ring
  have sharpIdentity : location ^ 4 * prepared.mixedSelectedFinerSourcePrefixBudget receiver incomingConstant outgoingConstant extent coefficient
      entry initialDistance magnitude weight finish =
      incomingConstant * extent ^ 2 * (location ^ 4 * ∑ source ∈ finer, sharp source) +
        outgoingConstant * (∑ source ∈ finer.filter (fun source => entry source < finish), later source) := by
    change location ^ 4 * (incomingConstant * extent ^ 2 * (∑ source ∈ finer, sharp source) +
      (outgoingConstant / location ^ 4) * (∑ source ∈ finer.filter (fun source => entry source < finish), later source)) = _
    field_simp [locationPositive.ne']
    ring
  rw [← commonIdentity, ← sharpIdentity] at combined
  have budgetBound : prepared.mixedFollowerSourcePrefixBudget receiver incomingConstant outgoingConstant extent coefficient
      entry initialDistance magnitude weight finish ≤ location ^ 3 *
      prepared.mixedSelectedFinerSourcePrefixBudget receiver incomingConstant outgoingConstant extent coefficient
        entry initialDistance magnitude weight finish := by
    apply (mul_le_mul_left locationPositive).mp
    convert combined using 1
    ring
  have sharpBudgetNonnegative : 0 ≤ prepared.mixedSelectedFinerSourcePrefixBudget receiver incomingConstant outgoingConstant extent coefficient
      entry initialDistance magnitude weight finish := by
    change 0 ≤ incomingConstant * extent ^ 2 * (∑ source ∈ finer, sharp source) +
      (outgoingConstant / location ^ 4) * (∑ source ∈ finer.filter (fun source => entry source < finish), later source)
    exact add_nonneg (mul_nonneg (mul_nonneg incomingNonnegative (sq_nonneg extent)) (Finset.sum_nonneg sharpNonnegative))
      (mul_nonneg (div_nonneg outgoingNonnegative (pow_nonneg locationPositive.le 4)) laterSumNonnegative)
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (receiver.val + 1)
  have frequencyBound : scales.frequency ≤ scales.omega (receiver.val + 1) * location := by
    have powerBound := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ratioBound (receiver.val + 1)
    change scales.frequency ≤ (scales.frequency * scales.ratio ^ (receiver.val + 1)) * scales.location (receiver.val + 1)
    rw [scales.location_eq_inv_pow]
    exact (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) (receiver.val + 1))).mpr
      (mul_le_mul_of_nonneg_left powerBound frequencyPositive.le)
  have returned := mul_le_mul_of_nonneg_left budgetBound
    (div_nonneg rhoNonnegative (mul_nonneg omegaPositive.le (pow_nonneg locationPositive.le 4)))
  have normalization : rho / (scales.omega (receiver.val + 1) * location ^ 4) * location ^ 3 =
      rho / (scales.omega (receiver.val + 1) * location) := by
    field_simp [locationPositive.ne', omegaPositive.ne']
    ring
  rw [← mul_assoc, normalization] at returned
  have frequencyGain : rho / (scales.omega (receiver.val + 1) * location) ≤ rho / scales.frequency :=
    (div_le_div_iff₀ (mul_pos omegaPositive locationPositive) frequencyPositive).mpr
      (mul_le_mul_of_nonneg_left frequencyBound rhoNonnegative)
  exact returned.trans (mul_le_mul_of_nonneg_right frequencyGain sharpBudgetNonnegative)

end EulerNonuniqueness.Paper
