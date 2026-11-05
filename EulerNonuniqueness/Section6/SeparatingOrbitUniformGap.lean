import EulerNonuniqueness.Section6.NormalizedPointOrbit

noncomputable section

namespace EulerNonuniqueness.Section6

theorem central_configuration_pair_gap {positive negative : ℂ} {gap : ℝ}
    (positiveGap : gap ≤ 2 * ‖positive‖) (negativeGap : gap ≤ 2 * ‖negative‖)
    (differenceGap : gap ≤ ‖positive - negative‖) (sumGap : gap ≤ ‖positive + negative‖)
    (target source : Fin 4) (different : target ≠ source) :
    gap ≤ ‖centrallySymmetricFourPoint positive negative target -
      centrallySymmetricFourPoint positive negative source‖ := by
  have positiveDouble : gap ≤ ‖positive + positive‖ := by
    simpa only [← two_mul, norm_mul, Complex.norm_ofNat] using positiveGap
  have negativeDouble : gap ≤ ‖negative + negative‖ := by
    simpa only [← two_mul, norm_mul, Complex.norm_ofNat] using negativeGap
  fin_cases target <;> fin_cases source <;>
    simp only [Fin.isValue, ne_eq, not_true_eq_false] at different
  all_goals simp [centrallySymmetricFourPoint]
  all_goals solve
    | exact positiveDouble
    | exact negativeDouble
    | exact differenceGap
    | exact sumGap
    | simpa only [norm_sub_rev] using differenceGap
    | simpa only [add_comm] using sumGap
    | simpa only [← neg_add, norm_neg] using positiveDouble
    | simpa only [← neg_add, norm_neg] using negativeDouble
    | convert sumGap using 1 <;> congr 1 <;> ring
    | convert differenceGap using 1 <;> congr 1 <;> ring
    | rw [← norm_neg]; convert sumGap using 1 <;> congr 1 <;> ring
    | rw [← norm_neg]; convert differenceGap using 1 <;> congr 1 <;> ring
    | convert positiveDouble using 1 <;> congr 1 <;> ring
    | convert negativeDouble using 1 <;> congr 1 <;> ring
    | rw [← norm_neg]; convert positiveDouble using 1 <;> congr 1 <;> ring
    | rw [← norm_neg]; convert negativeDouble using 1 <;> congr 1 <;> ring

theorem normalizedSeparatingOrbit_uniform_pair_gap
    (orbit : EulerNonuniqueness.Paper.SeparatingOrbit)
    (normalized : EulerNonuniqueness.Paper.IsNormalizedSeparatingOrbit orbit) :
    ∃ gap > (0 : ℝ), ∀ time : ℝ, ∀ target source : Fin 4, target ≠ source →
      gap ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (-orbit.negative time) target -
        centrallySymmetricFourPoint (orbit.positive time) (-orbit.negative time) source‖ := by
  obtain ⟨gap, positive, separated⟩ := normalized.2.2.1
  refine ⟨gap, positive, ?_⟩
  intro time target source different
  have bounds := separated time
  exact central_configuration_pair_gap bounds.1 (by simpa only [norm_neg] using bounds.2.1)
    (by simpa only [sub_neg_eq_add] using bounds.2.2.2)
    (by simpa only [← sub_eq_add_neg] using bounds.2.2.1) target source different

end EulerNonuniqueness.Section6
