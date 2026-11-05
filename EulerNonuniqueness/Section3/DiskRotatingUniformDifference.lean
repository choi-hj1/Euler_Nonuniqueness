import EulerNonuniqueness.Section3.DiskRotatingUniformTaylor

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] rotatingSecondFrechetC1Group secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace

theorem diskEulerRotatingField_exists_uniform_derivative_difference :
    ∃ radius > 0, radius ≤ 1 ∧ ∃ constant ≥ 1, ∀ data direction : PeriodicC1HolderHalf,
      ‖data - standardCircleBanach‖ + ‖direction‖ ≤ radius →
      ‖fderiv ℝ diskEulerRotatingField (data + direction) - fderiv ℝ diskEulerRotatingField data‖ ≤
        constant * ‖direction‖ := by
  obtain ⟨radius, positive, radiusOne, constant, constantOne, bounds⟩ :=
    diskEulerRotatingField_exists_uniform_firstJet_bounds
  refine ⟨radius, positive, radiusOne, 2 * constant, by linarith, ?_⟩
  intro data direction inside
  obtain ⟨_, secondBound, _, remainder⟩ := bounds data direction inside
  have small : ‖direction‖ ≤ 1 :=
    (le_add_of_nonneg_left (norm_nonneg (data - standardCircleBanach))).trans (inside.trans radiusOne)
  have quadraticSmall : ‖direction‖ ^ 2 ≤ ‖direction‖ := by nlinarith [norm_nonneg direction]
  have linearBound : ‖fderiv ℝ (fderiv ℝ diskEulerRotatingField) data direction‖ ≤ constant * ‖direction‖ :=
    ((fderiv ℝ (fderiv ℝ diskEulerRotatingField) data).le_opNorm direction).trans
      (mul_le_mul_of_nonneg_right secondBound (norm_nonneg _))
  have triangle := norm_add_le
    (fderiv ℝ diskEulerRotatingField (data + direction) - fderiv ℝ diskEulerRotatingField data -
      fderiv ℝ (fderiv ℝ diskEulerRotatingField) data direction)
    (fderiv ℝ (fderiv ℝ diskEulerRotatingField) data direction)
  rw [sub_add_cancel] at triangle
  exact triangle.trans ((add_le_add
    (remainder.trans (mul_le_mul_of_nonneg_left quadraticSmall (by linarith))) linearBound).trans_eq (by ring))

theorem diskEulerRotatingField_exists_uniform_shifted_self_error :
    ∃ radius > 0, ∃ constant ≥ 1, ∀ (data correction : PeriodicC1HolderHalf) (frequency : ℝ),
      ‖data - standardCircleBanach‖ + ‖correction‖ ≤ radius →
      ‖frequency • diskEulerRotatingField data -
        frequency • (fderiv ℝ diskEulerRotatingField data correction) -
        frequency • diskEulerRotatingField (data - correction)‖ ≤
          |frequency| * constant * ‖correction‖ ^ 2 := by
  obtain ⟨radius, positive, _, constant, constantOne, bounds⟩ :=
    diskEulerRotatingField_exists_uniform_firstJet_bounds
  refine ⟨radius, positive, constant, constantOne, ?_⟩
  intro data correction frequency inside
  have remainder := (bounds data (-correction) (by simpa only [norm_neg] using inside)).2.2.1
  have identity : diskEulerRotatingField data - fderiv ℝ diskEulerRotatingField data correction -
      diskEulerRotatingField (data - correction) =
      -(diskEulerRotatingField (data + -correction) - diskEulerRotatingField data -
        fderiv ℝ diskEulerRotatingField data (-correction)) := by
    rw [map_neg, ← sub_eq_add_neg]
    abel
  rw [← smul_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, identity, norm_neg]
  exact (mul_le_mul_of_nonneg_left (by simpa only [norm_neg] using remainder) (abs_nonneg frequency)).trans_eq (by ring)

end EulerNonuniqueness.Paper
