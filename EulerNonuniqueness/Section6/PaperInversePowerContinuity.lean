import EulerNonuniqueness.Section6.PaperMovingMomentContinuity
import EulerNonuniqueness.Section6.SmoothConjugateInversePower

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.continuousOn_patch_moving_inverse_power_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (separated : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    (index : Fin count) (patch : Fin 4) {center : ℝ → ℂ}
    (centerContinuous : ContinuousOn center (Icc 0 horizon))
    {distance : ℝ} (distancePositive : 0 < distance)
    (gap : ∀ current ∈ Icc 0 horizon, ∀ position ∈ motion.domain current index patch,
      distance ≤ ‖center current - position‖) (power : ℕ) :
    ContinuousOn (fun current => ∫ position, patchDensity scales motion current index patch position •
      (star (center current - position))⁻¹ ^ power) (Icc 0 horizon) := by
  obtain ⟨radius, radiusPositiveGlobal, domains⟩ :=
    evolution.exists_uniform_domain_support_of_boundary_control radiusPositive control
  obtain ⟨centerBound, centerBounded⟩ := isCompact_Icc.exists_bound_of_continuousOn centerContinuous
  let cutoff : ContDiffBump (0 : ℂ) :=
    ⟨radius + max centerBound 0 + 2, radius + max centerBound 0 + 3,
      by positivity, by linarith⟩
  let test : ℂ → ℂ := fun argument => (cutoff argument : ℂ) *
    Section6.smoothConjugateInversePower distance power argument
  have testContinuous : Continuous test :=
    (Complex.continuous_ofReal.comp cutoff.continuous).mul
      (Section6.smoothConjugateInversePower_contDiff distancePositive power).continuous
  have compact : HasCompactSupport test :=
    (cutoff.hasCompactSupport.comp_left (g := fun value : ℝ => (value : ℂ)) (by simp)).mul_right
  have result := evolution.continuousOn_patch_moving_compact_moment_of_boundary_gaps
    radiusPositive control separated index patch centerContinuous testContinuous compact
  apply result.congr
  intro current member
  apply integral_congr_ae
  apply Eventually.of_forall
  intro position
  by_cases inDomain : position ∈ motion.domain current index patch
  · have positionBound : ‖position‖ ≤ radius := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using domains current member index patch inDomain
    have argumentInside : center current - position ∈ Metric.ball (0 : ℂ) cutoff.rIn := by
      simp only [Metric.mem_ball, dist_zero_right]
      change ‖center current - position‖ < radius + max centerBound 0 + 2
      have triangle := norm_sub_le (center current) position
      linarith only [triangle, positionBound, centerBounded current member, le_max_left centerBound 0]
    have one := (cutoff.eventuallyEq_one_of_mem_ball argumentInside).self_of_nhds
    have kernel := (Section6.smoothConjugateInversePower_eventuallyEq distancePositive power
      (gap current member position inDomain)).self_of_nhds
    change patchDensity scales motion current index patch position • _ =
      patchDensity scales motion current index patch position • _
    simp only [test, one, Pi.one_apply, Complex.ofReal_one, one_mul, kernel]
  · simp only [patchDensity, indicator_of_not_mem inDomain, zero_smul]

end EulerNonuniqueness.Paper
