import EulerNonuniqueness.Section6.SignedInversePowerBound
import EulerNonuniqueness.Section6.FourPointTranslationControl

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointSignedMoment_centered (positions : FourPointConfiguration) (center : ℂ) :
    fourPointSignedMoment (fun patch => positions patch - center) = fourPointSignedMoment positions := by
  simp [fourPointSignedMoment, fourPointSign, Fin.sum_univ_succ]
  ring

theorem fourPointSignedMoment_sub (first second : FourPointConfiguration) :
    fourPointSignedMoment (fun patch => first patch - second patch) =
      fourPointSignedMoment first - fourPointSignedMoment second := by
  simp only [fourPointSignedMoment, mul_sub, Finset.sum_sub_distrib]

theorem fourPoint_inverse_power_relative_bound (first second : FourPointConfiguration)
    (displacement : ℂ) (power : ℕ) {radius distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (separated : radius + distance ≤ ‖displacement‖)
    (firstBound : ∀ patch, ‖first patch‖ ≤ radius)
    (secondBound : ∀ patch, ‖second patch‖ ≤ radius) :
    ‖(∑ patch : Fin 4, fourPointSign patch • (star (displacement - first patch))⁻¹ ^ (power + 1)) -
      (∑ patch : Fin 4, fourPointSign patch • (star (displacement - second patch))⁻¹ ^ (power + 1))‖ ≤
      ((power + 1 : ℝ) * distance⁻¹ ^ (power + 2)) *
        ‖fourPointSignedMoment first - fourPointSignedMoment second‖ +
      ((power + 1 : ℝ) * (power + 2 : ℝ) * distance⁻¹ ^ (power + 3) * radius) *
        ∑ patch : Fin 4, ‖first patch - second patch‖ := by
  have momentIdentity :
      (∑ patch : Fin 4, fourPointSign patch • (first patch - second patch)) =
        fourPointSignedMoment first - fourPointSignedMoment second := by
    simp only [Complex.real_smul, ← fourPointSignedMoment_sub]
    rfl
  have absoluteSign (patch : Fin 4) : |fourPointSign patch| = 1 := by
    unfold fourPointSign
    split_ifs <;> norm_num
  simpa only [momentIdentity, absoluteSign, one_mul] using
    signed_inverse_power_relative_bound Finset.univ fourPointSign first second displacement power
      radiusNonnegative positive separated (fun patch _ => firstBound patch) (fun patch _ => secondBound patch)

theorem fourPoint_centered_inverse_power_relative_bound (first second : FourPointConfiguration)
    (firstCenter secondCenter displacement : ℂ) (power : ℕ) {radius distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (separated : radius + distance ≤ ‖displacement‖)
    (firstBound : ∀ patch, ‖first patch - firstCenter‖ ≤ radius)
    (secondBound : ∀ patch, ‖second patch - secondCenter‖ ≤ radius) :
    ‖(∑ patch : Fin 4, fourPointSign patch •
        (star (displacement - (first patch - firstCenter)))⁻¹ ^ (power + 1)) -
      (∑ patch : Fin 4, fourPointSign patch •
        (star (displacement - (second patch - secondCenter)))⁻¹ ^ (power + 1))‖ ≤
      ((power + 1 : ℝ) * distance⁻¹ ^ (power + 2)) *
        ‖fourPointSignedMoment first - fourPointSignedMoment second‖ +
      ((power + 1 : ℝ) * (power + 2 : ℝ) * distance⁻¹ ^ (power + 3) * radius) *
        ∑ patch : Fin 4, ‖(first patch - firstCenter) - (second patch - secondCenter)‖ := by
  simpa only [fourPointSignedMoment_centered] using
    fourPoint_inverse_power_relative_bound (fun patch => first patch - firstCenter)
      (fun patch => second patch - secondCenter) displacement power
      radiusNonnegative positive separated firstBound secondBound

end EulerNonuniqueness.Section6
