import EulerNonuniqueness.Section3.CanonicalExteriorCommonNormalizedDerivative

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

theorem canonicalExteriorCommonNormalizedPhysicalDerivative_exists_norm_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count) (frequency time : ℝ)
        (data : PeriodicC1HolderHalf),
      ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time data - standardCircleBanach‖ ≤ radius →
      ‖family.canonicalExteriorCommonNormalizedPhysicalDerivative index frequency time data‖ ≤
        constant * ‖family.canonicalExteriorCommonPhysicalDerivative index frequency time data‖ := by
  obtain ⟨radius, positive, constant, one, relative⟩ := diskNormalizedSpectralError_exists_relative_ball
  refine ⟨radius, positive, constant, one, ?_⟩
  intro count family index frequency time data nearby
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  have actual := relative
    (family.canonicalExteriorCommonPhysicalCoordinate index frequency time data)
    (family.canonicalExteriorCommonPhysicalCoordinate index frequency time data)
    (family.canonicalExteriorCommonPhysicalDerivative index frequency time data direction) 0 nearby nearby
  simp only [diskNormalizedSpectralError, map_zero, sub_zero, sub_self, norm_zero, zero_mul, add_zero] at actual
  have scalar := mul_le_mul_of_nonneg_left
    ((family.canonicalExteriorCommonPhysicalDerivative index frequency time data).le_opNorm direction)
    (by linarith : 0 ≤ constant)
  exact (actual.trans scalar).trans_eq (by ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
