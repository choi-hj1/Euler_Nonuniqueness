import EulerNonuniqueness.Section5.CascadeForeignMomentBound
import EulerNonuniqueness.Section4.ReferenceStatement

noncomputable section

namespace EulerNonuniqueness.Paper

theorem cascade_internal_deformation_speed_le {omega length radius factor : ℝ}
    (omegaPositive : 0 < omega) (lengthPositive : 0 < length) (radiusNonnegative : 0 ≤ radius)
    (factorPositive : 0 < factor) (radiusSmall : radius ≤ factor * length / 1000) :
    3456 * (2 * Real.pi * omega * length ^ 2) * radius ^ 2 * (1 / 16) /
      (Real.pi * (factor * length) ^ 3) ≤ omega * length / factor := by
  have productPositive : 0 < factor * length := mul_pos factorPositive lengthPositive
  have ratioNonnegative : 0 ≤ radius / (factor * length) := div_nonneg radiusNonnegative productPositive.le
  have ratioBound : radius / (factor * length) ≤ 1 / 1000 := by
    apply (div_le_iff₀ productPositive).mpr
    linarith
  have ratioSquare : (radius / (factor * length)) ^ 2 ≤ (1 / 1000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ ratioNonnegative ratioBound 2
  have identity : 3456 * (2 * Real.pi * omega * length ^ 2) * radius ^ 2 * (1 / 16) /
      (Real.pi * (factor * length) ^ 3) =
        (432 * omega * length / factor) * (radius / (factor * length)) ^ 2 := by
    field_simp [Real.pi_ne_zero, lengthPositive.ne', factorPositive.ne']
    <;> ring
  rw [identity]
  have weighted := mul_le_mul_of_nonneg_left ratioSquare
    (by positivity : 0 ≤ 432 * omega * length / factor)
  have mainNonnegative : 0 ≤ omega * length / factor := by positivity
  have coefficient : 432 * omega * length / factor = 432 * (omega * length / factor) := by ring
  rw [coefficient] at weighted ⊢
  generalize omega * length / factor = main at weighted mainNonnegative ⊢
  nlinarith

theorem Scales.cascadeForeignStrain_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {factor : ℝ} (factorPositive : 0 < factor)
    (receiver : Fin count) :
    (∑ source ∈ Finset.univ.erase receiver,
      2 * scales.circulation (source.val + 1) /
        (Real.pi * cascadeForeignDistance scales factor receiver source ^ 2)) ≤
      (2 / Real.pi) * (24 / factor) ^ 2 * scales.strain := by
  have identity : (∑ source ∈ Finset.univ.erase receiver,
      2 * scales.circulation (source.val + 1) /
        (Real.pi * cascadeForeignDistance scales factor receiver source ^ 2)) =
      (2 / Real.pi) * (∑ source ∈ Finset.univ.erase receiver,
        scales.circulation (source.val + 1) / cascadeForeignDistance scales factor receiver source ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    ring
  rw [identity]
  have actual := mul_le_mul_of_nonneg_left
    (scales.sum_cascadeForeignMoment_le frequencyBound ratioBound alphaPositive factorPositive receiver 2)
    (by positivity : 0 ≤ 2 / Real.pi)
  simpa only [Scales.strain, mul_assoc] using actual

end EulerNonuniqueness.Paper
