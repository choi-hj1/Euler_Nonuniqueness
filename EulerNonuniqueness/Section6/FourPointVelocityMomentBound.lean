import EulerNonuniqueness.Section6.PointSourceVelocityRelative
import EulerNonuniqueness.Section6.SourcePacketVelocityPhysicalBound

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointExternalPointVelocity_moment_bound
    (positions : FourPointConfiguration) (center location : ℂ) (coefficient : ℝ) {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius) (distancePositive : 0 < ‖location - center‖)
    (separated : 2 * radius ≤ ‖location - center‖)
    (positionBound : ∀ patch, ‖positions patch - center‖ ≤ radius) :
    ‖fourPointExternalPointVelocity coefficient positions location‖ ≤
      |coefficient| * (4 * ‖fourPointSignedMoment positions‖ / ‖location - center‖ ^ 2 +
        64 * radius ^ 2 / ‖location - center‖ ^ 3) := by
  let offsets : FourPointConfiguration := fun patch => positions patch - center
  have translation : fourPointExternalPointVelocity coefficient offsets (location - center) =
      fourPointExternalPointVelocity coefficient positions location := by
    simp only [fourPointExternalPointVelocity, fourPointCauchyField, offsets, sub_sub_sub_cancel_right]
  have zeroField : fourPointExternalPointVelocity coefficient (fun _ => 0) (location - center) = 0 := by
    have zeroCauchy : fourPointCauchyField (fun _ => 0) (location - center) = 0 := by
      simp [fourPointCauchyField, fourPointSign, Fin.sum_univ_succ]
      ring
    rw [fourPointExternalPointVelocity, zeroCauchy, star_zero, mul_zero]
  have zeroMoment : fourPointSignedMoment (fun _ => 0) = 0 := by simp [fourPointSignedMoment]
  have actual := fourPointExternalPointVelocity_configuration_difference_bound offsets (fun _ => 0)
    (location - center) coefficient radiusNonnegative (half_pos distancePositive) (by linarith)
    positionBound (fun _ => by simpa only [norm_zero] using radiusNonnegative)
  rw [translation, zeroField, sub_zero, zeroMoment, sub_zero, fourPointSignedMoment_centered] at actual
  have total : (∑ patch : Fin 4, ‖offsets patch - 0‖) ≤ 4 * radius := by
    have bound := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => positionBound patch)
    simpa only [sub_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, offsets] using bound
  apply actual.trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg coefficient)
  have compared := add_le_add_left
    (mul_le_mul_of_nonneg_left total
      (show 0 ≤ 2 * (‖location - center‖ / 2)⁻¹ ^ 3 * radius by positivity))
    ((‖location - center‖ / 2)⁻¹ ^ 2 * ‖fourPointSignedMoment positions‖)
  apply compared.trans_eq
  field_simp; ring

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

open Set EulerNonuniqueness.Section6

theorem FinitePatchEvolution.quadrupole_velocity_moment_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation gap radius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (location center : ℂ)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1 / 16)
    (gapPositive : 0 < gap) (radiusSmall : 4 * scales.radius (index.val + 1) ≤ gap)
    (centroidsSeparated : ∀ patch, gap ≤ ‖location - patchCentroid motion time index patch‖)
    (radiusNonnegative : 0 ≤ radius) (distancePositive : 0 < ‖location - center‖)
    (far : 2 * radius ≤ ‖location - center‖)
    (centroidBound : ∀ patch, ‖patchCentroid motion time index patch - center‖ ≤ radius) :
    ‖biotSavart (quadrupoleDensity scales motion time index) location‖ ≤
      (scales.circulation (index.val + 1) / (2 * Real.pi)) *
        (4 * ‖fourPointSignedMoment (fun patch => patchCentroid motion time index patch)‖ / ‖location - center‖ ^ 2 +
          64 * radius ^ 2 / ‖location - center‖ ^ 3) +
      512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
        (Real.pi * gap ^ 3) := by
  have correction := evolution.quadrupole_velocity_point_error_of_boundaryControl inside amplitudePositive frequencyPositive
    ratioPositive index location control deformationNonnegative deformationSmall gapPositive radiusSmall centroidsSeparated
  have point := fourPointExternalPointVelocity_moment_bound
    (fun patch => patchCentroid motion time index patch) center location
    (scales.circulation (index.val + 1) / (2 * Real.pi)) radiusNonnegative distancePositive far centroidBound
  rw [abs_of_nonneg (div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (by positivity))] at point
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (biotSavart (quadrupoleDensity scales motion time index) location)
    (fourPointExternalPointVelocity (scales.circulation (index.val + 1) / (2 * Real.pi))
      (fun patch => patchCentroid motion time index patch) location) 0
  simp only [sub_zero] at triangle
  exact triangle.trans ((add_le_add correction point).trans_eq (add_comm _ _))

end EulerNonuniqueness.Paper
