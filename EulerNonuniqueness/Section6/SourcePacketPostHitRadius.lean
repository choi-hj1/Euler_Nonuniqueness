import EulerNonuniqueness.Section6.SourcePacketActualPostHitContinuation

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem source_packet_posthit_width_and_radius {count : ℕ} (motion : PatchMotion count)
    (index : Fin count) (time : ℝ) {length omega initialDistance elapsed patchRadius : ℝ} {direction : ℂ}
    (lengthPositive : 0 < length) (omegaLarge : 64 ≤ omega) (elapsedUpper : elapsed ≤ 1)
    (initialDistanceSmall : initialDistance ≤ omega / 16) (directionNorm : ‖direction‖ = 1)
    (firstTracked : ‖firstDipoleSeparation motion time index - (length : ℂ) * direction‖ ≤ length / 16)
    (secondTracked : ‖secondDipoleSeparation motion time index - (length : ℂ) * (-direction)‖ ≤ length / 16)
    (pairUpper : ‖firstDipoleCenter motion time index - secondDipoleCenter motion time index‖ ≤
      3 * length * (initialDistance + omega * elapsed))
    (radiusNonnegative : 0 ≤ patchRadius) (radiusSmall : patchRadius ≤ length / 1000)
    (domains : ∀ patch, motion.domain time index patch ⊆
      closedBall (patchCentroid motion time index patch) (2 * patchRadius)) :
    ‖firstDipoleSeparation motion time index‖ ≤ 2 * length ∧
    ‖secondDipoleSeparation motion time index‖ ≤ 2 * length ∧
    (∀ patch, ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ≤ 4 * omega * length) ∧
    (∀ patch, motion.domain time index patch ⊆ closedBall (quadrupoleCenter motion time index) (4 * omega * length)) := by
  have idealNorm : ‖(length : ℂ) * direction‖ = length := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos lengthPositive, directionNorm, mul_one]
  have first := (dipole_separation_norm_bounds length lengthPositive directionNorm firstTracked).2
  have second := (dipole_separation_norm_bounds length lengthPositive
    (show ‖-direction‖ = 1 by simpa using directionNorm) secondTracked).2
  have pairScalar : ‖firstDipoleCenter motion time index - secondDipoleCenter motion time index‖ / 2 +
      2 * patchRadius + length ≤ 4 * omega * length := by
    have timeBound := mul_le_mul_of_nonneg_left elapsedUpper (show 0 ≤ omega by linarith)
    have sumBound : initialDistance + omega * elapsed ≤ omega / 16 + omega :=
      add_le_add initialDistanceSmall (by simpa only [mul_one] using timeBound)
    have product := mul_le_mul_of_nonneg_left sumBound (show 0 ≤ 3 * length by positivity)
    have largeProduct := mul_le_mul_of_nonneg_right omegaLarge lengthPositive.le
    nlinarith
  have centroidBound (patch : Fin 4) :
      ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ≤ 4 * omega * length := by
    have near := patchCentroid_near_dipole_center motion time index first second patch
    have middle : dist (quadrupoleCenter motion time index)
        (midpoint ℝ (firstDipoleCenter motion time index) (secondDipoleCenter motion time index)) ≤ (0 : ℝ) := by
      rw [quadrupoleCenter_eq_dipole_midpoint, dist_self]
    by_cases firstPair : patch = 0 ∨ patch = 3
    · rw [if_pos firstPair] at near
      have bound := (dist_annulus_of_dist_midpoint_le near middle).2
      rw [dist_eq_norm, dist_eq_norm] at bound
      linarith
    · rw [if_neg firstPair] at near
      have reverse : dist (quadrupoleCenter motion time index)
          (midpoint ℝ (secondDipoleCenter motion time index) (firstDipoleCenter motion time index)) ≤ (0 : ℝ) := by
        simpa only [midpoint_comm] using middle
      have bound := (dist_annulus_of_dist_midpoint_le near reverse).2
      rw [dist_comm (secondDipoleCenter motion time index), dist_eq_norm, dist_eq_norm] at bound
      linarith
  refine ⟨first, second, centroidBound, ?_⟩
  intro patch position member
  have bound := (quadrupole_domain_annular_estimate first second
    (centerError := 0) (by rw [sub_self, norm_zero]) domains patch position member).2
  rw [pairCenterDistance_eq_dist, dist_eq_norm] at bound
  rw [mem_closedBall, dist_eq_norm]
  linarith

end EulerNonuniqueness.Paper
