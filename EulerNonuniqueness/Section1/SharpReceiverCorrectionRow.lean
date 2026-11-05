import EulerNonuniqueness.Section1.MultipoleInteractionRow
import EulerNonuniqueness.Section1.UniformInitialScaleSmallness

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.sharp_receiver_correction_row_le {count : ℕ} (scales : Scales)
    (frequencyOne : 1 ≤ scales.frequency) (ratioTwo : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (receiver : Fin count) (selected : Finset (Fin count))
    (different : ∀ source ∈ selected, source ≠ receiver)
    (lengthSmall : ∀ source ∈ selected, scales.length (source.val + 1) ≤ scales.location (source.val + 1)) :
    (∑ source ∈ selected, scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2 /
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| ^ 5) ≤
      243 * scales.hessian := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioTwo]
  have termNonnegative (source : Fin count) :
      0 ≤ scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 3 :=
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (scales.location_pos _).le _)
  have individual (source : Fin count) (member : source ∈ selected) :
      scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2 /
        |scales.location (receiver.val + 1) - scales.location (source.val + 1)| ^ 5 ≤
      243 * (scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 3) := by
    have indicesDifferent : receiver.val + 1 ≠ source.val + 1 := by
      intro equality
      exact different source member (Fin.ext (Nat.add_right_cancel equality).symm)
    have locationPositive := scales.location_pos (source.val + 1)
    have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive (source.val + 1)).le
    have locations := scales.location_sum_le_three_distance indicesDifferent
    have distanceLower : scales.location (source.val + 1) / 3 ≤
        |scales.location (receiver.val + 1) - scales.location (source.val + 1)| := by
      linarith only [locations, (scales.location_pos (receiver.val + 1)).le]
    have squareBound := pow_le_pow_left₀ (scales.length_pos (source.val + 1)).le (lengthSmall source member) 2
    calc
      _ ≤ scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2 /
          (scales.location (source.val + 1) / 3) ^ 5 :=
        div_le_div_of_nonneg_left
          (mul_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
          (pow_pos (div_pos locationPositive (by norm_num)) _)
          (pow_le_pow_left₀ (div_nonneg locationPositive.le (by norm_num)) distanceLower 5)
      _ = (243 * scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 5) *
          scales.length (source.val + 1) ^ 2 := by
        (field_simp; ring)
      _ ≤ (243 * scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 5) *
          scales.location (source.val + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left squareBound (by positivity)
      _ = _ := by
        (field_simp [locationPositive.ne']; ring)
  have finiteBound : (∑ source ∈ selected,
      scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 3) ≤ scales.hessian := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
      (fun source _ _ => termNonnegative source)).trans
    rw [Fin.sum_univ_eq_sum_range (fun source : ℕ =>
      scales.circulation (source + 1) / scales.location (source + 1) ^ 3) count]
    exact (scales.circulation_location_summable frequencyOne ratioTwo alphaPositive 3).sum_le_tsum
      (Finset.range count) (fun source _ => div_nonneg
        (scales.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (scales.location_pos _).le _))
  calc
    _ ≤ ∑ source ∈ selected, 243 * (scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 3) :=
      Finset.sum_le_sum individual
    _ = 243 * ∑ source ∈ selected, scales.circulation (source.val + 1) / scales.location (source.val + 1) ^ 3 :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left finiteBound (by norm_num)

theorem Scales.eventually_sharp_receiver_correction_row_small (scales : Scales)
    (ratioTwo : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {constant extent tolerance : ℝ} (constantNonnegative : 0 ≤ constant) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ receiver : Fin count, ∀ selected : Finset (Fin count),
      (∀ source ∈ selected, source ≠ receiver) →
      let changed : Scales := {scales with frequency := frequency}
      constant * extent ^ 2 *
        (∑ source ∈ selected, changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 /
          |changed.location (receiver.val + 1) - changed.location (source.val + 1)| ^ 5) < tolerance := by
  have decay := ((scales.hessian_tendsto_zero ratioTwo alphaPositive).const_mul
    (constant * extent ^ 2 * 243)).eventually (eventually_lt_nhds (by
      simpa only [mul_zero] using tolerancePositive))
  filter_upwards [decay, eventually_ge_atTop (1 : ℝ),
    scales.eventually_length_lt_location ratioTwo alphaPositive (by norm_num : (0 : ℝ) < 1)]
    with frequency small frequencyOne lengths
  intro count receiver selected different
  dsimp only
  have row := (Scales.sharp_receiver_correction_row_le {scales with frequency := frequency}
    frequencyOne ratioTwo alphaPositive receiver selected different (fun source _ => by
      simpa only [one_mul] using (lengths (source.val + 1)).le))
  have scaled := mul_le_mul_of_nonneg_left row (mul_nonneg constantNonnegative (sq_nonneg extent))
  exact scaled.trans_lt (by simpa only [mul_assoc] using small)

end EulerNonuniqueness.Paper
