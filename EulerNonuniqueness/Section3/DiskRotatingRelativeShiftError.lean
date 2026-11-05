import EulerNonuniqueness.Section3.DiskRotatingPhysicalRelativeTaylor

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

local instance rotatingRelativeShiftC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskRotatingShiftError (current displacement : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskEulerRotatingField current - fderiv ℝ diskEulerRotatingField current displacement -
    diskEulerRotatingField (current - displacement)

theorem diskRotatingShiftError_eq_neg_taylor (current displacement : PeriodicC1HolderHalf) :
    diskRotatingShiftError current displacement = -diskRotatingTaylorRemainder current (-displacement) := by
  unfold diskRotatingShiftError diskRotatingTaylorRemainder
  simp only [map_neg, ← sub_eq_add_neg]
  abel

theorem diskRotatingShiftError_exists_scaled_relative_ball :
    ∃ radius > 0, ∃ constant ≥ 0,
      ∀ initial final initialShift finalShift : PeriodicC1HolderHalf,
      ‖initial - standardCircleBanach‖ + (‖initialShift‖ + ‖finalShift‖) ≤ radius →
      ‖final - standardCircleBanach‖ + (‖initialShift‖ + ‖finalShift‖) ≤ radius →
      ∀ frequency : ℝ,
      ‖frequency • diskRotatingShiftError initial initialShift -
        frequency • diskRotatingShiftError final finalShift‖ ≤
      constant * |frequency| *
        ((‖initialShift‖ + ‖finalShift‖) * ‖initialShift - finalShift‖ +
          ‖initial - final‖ * ‖finalShift‖ ^ 2) := by
  obtain ⟨radius, positive, constant, taylor⟩ :=
    diskRotatingTaylorRemainder_exists_relative_quadratic_ball
  refine ⟨radius, positive, (constant : ℝ), constant.coe_nonneg, ?_⟩
  intro initial final initialShift finalShift initialInside finalInside frequency
  have estimate := taylor initial final (-initialShift) (-finalShift)
    (by simpa only [norm_neg] using initialInside) (by simpa only [norm_neg] using finalInside)
  have negativeDifference : -initialShift - -finalShift = -(initialShift - finalShift) := by abel
  simp only [norm_neg, negativeDifference] at estimate
  have value : diskRotatingShiftError initial initialShift - diskRotatingShiftError final finalShift =
      -(diskRotatingTaylorRemainder initial (-initialShift) - diskRotatingTaylorRemainder final (-finalShift)) := by
    rw [diskRotatingShiftError_eq_neg_taylor, diskRotatingShiftError_eq_neg_taylor]
    abel
  rw [← smul_sub, value, norm_smul, norm_neg, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left estimate (abs_nonneg frequency)).trans_eq (by ring)

end EulerNonuniqueness.Paper
