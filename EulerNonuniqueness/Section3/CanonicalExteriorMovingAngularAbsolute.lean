import EulerNonuniqueness.Section3.CanonicalExteriorMovingAngularRate

noncomputable section

open Metric MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorCommonMovingAngularTerm_exists_actual_cubic_bound_ball :
    ∃ rawRadius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (state : PeriodicC1HolderHalf), state ∈ ball 0 rawRadius → diskSpectralTubularArea state = Real.pi →
      ∀ {frequency time distance weight radius : ℝ}, frequency ≠ 0 →
      ∀ (positive : 0 < distance) (weightNonnegative : 0 ≤ weight),
      0 ≤ radius → radius ≤ 1 → ‖diskPhysicalTransverseProjection state‖ ≤ radius →
      ∀ (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖),
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      weight / |frequency| ≤ radius → (weight / |frequency|) ^ 2 ≤ radius ^ 3 →
      ‖family.canonicalExteriorCommonMovingAngularTerm index frequency time distance positive
          (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart state)‖ ≤
        constant * |frequency| * radius ^ 3 := by
  obtain ⟨pairRadius, pairPositive, pairConstant, pairOne, pairs⟩ :=
    canonicalExteriorCommonMovingAngularTerm_exists_actual_quadratic_rate_ball
  obtain ⟨speedRadius, speedPositive, speedConstant, speedOne, speeds⟩ :=
    canonicalProjectedExteriorContourField_exists_true_angular_drift_bound_ball
  let rawRadius := min pairRadius (1 / (1 + ‖diskNeutralCLM‖))
  refine ⟨rawRadius, by dsimp only [rawRadius]; positivity, 2 * pairConstant + 1, by linarith, ?_⟩
  intro count family index state inside area frequency time distance weight radius nonzero positive weightNonnegative
    radiusNonnegative radiusSmall transverseSmall small separated weightBound epsilonSmall squaredSmall
  have angularSmall : ‖diskNeutralCLM state‖ ≤ 1 := by
    have stateSmall : ‖state‖ ≤ rawRadius := (by simpa only [mem_ball, dist_zero_right] using inside : ‖state‖ < rawRadius).le
    have scaled := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskNeutralCLM‖)).mp (stateSmall.trans (min_le_right _ _))
    nlinarith [diskNeutralCLM.le_opNorm state, norm_nonneg state]
  have zeroArea : diskSpectralTubularArea (0 : PeriodicC1HolderHalf) = Real.pi := by
    rw [diskSpectralTubularArea, diskSpectralTubularChart_zero, diskStationaryArea_zero]
  have speed := speeds family index standardCircleBanach (by simpa only [sub_self, norm_zero] using speedPositive)
    contourAreaFunctional_standardCircle time distance weight frequency positive weightNonnegative small separated weightBound
    (Circle.exp (frequency * time / 2))
  simp only [diskPhysicalSpectralCoordinate_circle, map_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, add_zero] at speed
  have driftZero := norm_eq_zero.mp (le_antisymm speed (norm_nonneg _))
  have movingZero : family.canonicalExteriorCommonMovingAngularTerm index frequency time distance positive
      (by linarith [(family.patch index).radius_positive]) separated standardCircleBanach = 0 := by
    unfold canonicalExteriorCommonMovingAngularTerm
    rw [driftZero, map_zero]
  have actual := pairs family index state 0 (ball_subset_ball (min_le_left _ _) inside)
    (mem_ball_zero_iff.mpr (by simpa using pairPositive)) area zeroArea nonzero positive weightNonnegative
    radiusNonnegative radiusSmall transverseSmall (by simpa only [map_zero, norm_zero] using radiusNonnegative)
    small separated weightBound epsilonSmall squaredSmall
  simp only [diskPhysicalSpectralChart_zero, movingZero, sub_zero, map_zero] at actual
  have weighted : ‖diskPhysicalTransverseProjection state‖ + radius * ‖diskNeutralCLM state‖ ≤ 2 * radius := by
    have scaled := mul_le_mul_of_nonneg_left angularSmall radiusNonnegative
    linarith
  have bounded := actual.trans (mul_le_mul_of_nonneg_left weighted (by positivity : 0 ≤ pairConstant * |frequency| * radius ^ 2))
  have scalar := mul_le_mul_of_nonneg_right (show 2 * pairConstant ≤ 2 * pairConstant + 1 by linarith)
    (by positivity : 0 ≤ |frequency| * radius ^ 3)
  exact (bounded.trans_eq (by ring)).trans (scalar.trans_eq (by ring))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
