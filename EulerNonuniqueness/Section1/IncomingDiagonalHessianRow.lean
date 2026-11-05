import EulerNonuniqueness.Section1.MultipoleInteractionRow
import EulerNonuniqueness.Section1.UniformInitialScaleSmallness

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_finite_incoming_diagonal_sum_le_hessian (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ selected : Finset (Fin count),
      let changed : Scales := {scales with frequency := frequency}
      (∑ source ∈ selected, changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 /
        changed.location (source.val + 1) ^ 4) ≤ changed.hessian := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1)]
    with frequency frequencyOne lengths
  intro count selected
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have termNonnegative (source : Fin count) :
      0 ≤ changed.circulation (source.val + 1) / changed.location (source.val + 1) ^ 3 :=
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (changed.location_pos _).le 3)
  have individual (source : Fin count) :
      changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 /
          changed.location (source.val + 1) ^ 4 ≤
        changed.circulation (source.val + 1) / changed.location (source.val + 1) ^ 3 := by
    have locationPositive := changed.location_pos (source.val + 1)
    have lengthBelow : changed.length (source.val + 1) ≤ changed.location (source.val + 1) := by
      simpa only [one_mul] using (lengths (source.val + 1)).le
    have squared : changed.length (source.val + 1) ^ 2 ≤ changed.location (source.val + 1) := by
      have power := pow_le_pow_left₀ (changed.length_pos _).le lengthBelow 2
      nlinarith only [power, locationPositive.le, changed.location_le_one (source.val + 1)]
    have actual := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left squared (changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)).le)
      (pow_nonneg locationPositive.le 4)
    exact actual.trans_eq (show changed.circulation (source.val + 1) * changed.location (source.val + 1) /
        changed.location (source.val + 1) ^ 4 = changed.circulation (source.val + 1) / changed.location (source.val + 1) ^ 3 by
      field_simp [locationPositive.ne']
      ring)
  have finiteHessian : (∑ source ∈ selected,
      changed.circulation (source.val + 1) / changed.location (source.val + 1) ^ 3) ≤ changed.hessian := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
      (fun source _ _ => termNonnegative source)).trans
    rw [Fin.sum_univ_eq_sum_range (fun source : ℕ => changed.circulation (source + 1) / changed.location (source + 1) ^ 3) count]
    exact (changed.circulation_location_summable frequencyOne ratioBound alphaPositive 3).sum_le_tsum
      (Finset.range count) (fun source _ => div_nonneg
        (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le 3))
  exact (Finset.sum_le_sum (s := selected) (fun source _ => individual source)).trans finiteHessian

end EulerNonuniqueness.Paper
