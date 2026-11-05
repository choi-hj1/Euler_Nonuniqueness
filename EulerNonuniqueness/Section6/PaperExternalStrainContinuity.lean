import EulerNonuniqueness.Section6.PaperInversePowerContinuity
import EulerNonuniqueness.Section6.PaperExteriorCoefficientDerivative

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.externalQuadrupoleStrain_continuousOn_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (separated : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    {center : ℝ → ℂ} (centerContinuous : ContinuousOn center (Icc 0 horizon))
    (index : Fin count) {distance : ℝ} (distancePositive : 0 < distance)
    (gap : ∀ current ∈ Icc 0 horizon, ∀ source ∈ Finset.univ.erase index, ∀ patch position,
      position ∈ motion.domain current source patch → distance ≤ ‖center current - position‖) :
    ContinuousOn (externalQuadrupoleStrain scales motion center index) (Icc 0 horizon) := by
  classical
  have individual (source : Fin count) (member : source ∈ Finset.univ.erase index) (patch : Fin 4) :=
    evolution.continuousOn_patch_moving_inverse_power_of_boundary_gaps radiusPositive control separated source patch
      centerContinuous distancePositive (fun current inside position inDomain => gap current inside source member patch position inDomain) 2
  have summed := continuousOn_finset_sum (Finset.univ.erase index) fun source member =>
    continuousOn_finset_sum Finset.univ fun patch _ => individual source member patch
  have weighted := continuousOn_const.mul summed (f := fun _ : ℝ => -Complex.I / (2 * Real.pi : ℂ))
  apply weighted.congr
  intro current member
  have identity := evolution.integral_externalPatch_inverse_power_eq_sum member index (center current) distancePositive
    (gap current member) 2 (field := fun _ => (1 : ℂ)) continuous_const
  simp only [one_mul] at identity
  change (-Complex.I / (2 * Real.pi : ℂ)) * _ = (-Complex.I / (2 * Real.pi : ℂ)) * _
  rw [identity]

end EulerNonuniqueness.Paper
