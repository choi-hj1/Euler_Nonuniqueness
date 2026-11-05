import EulerNonuniqueness.Section6.PaperMovingSmoothTransport
import EulerNonuniqueness.Section6.SmoothConjugateInversePower

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.hasDerivAt_patch_moving_inverse_power_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonPositive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (separated : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    (index : Fin count) (patch : Fin 4) (inside : time ∈ Ioo 0 horizon)
    {center : ℝ → ℂ} {velocity : ℂ} (centerDerivative : HasDerivAt center velocity time)
    {distance : ℝ} (distancePositive : 0 < distance)
    (separatedNear : ∀ᶠ current in 𝓝 time, ∀ position ∈ motion.domain current index patch,
      distance ≤ ‖center current - position‖) (power : ℕ) :
    HasDerivAt (fun current => ∫ position, patchDensity scales motion current index patch position •
        (star (center current - position))⁻¹ ^ (power + 1))
      (-((power + 1 : ℕ) : ℂ) * ∫ position, patchDensity scales motion time index patch position •
        (star (velocity - biotSavart (patchVorticity scales motion time) position) *
          (star (center time - position))⁻¹ ^ (power + 2))) time := by
  obtain ⟨radius, radiusPositiveGlobal, domains⟩ :=
    evolution.exists_uniform_domain_support_of_boundary_control radiusPositive control
  let cutoff : ContDiffBump (0 : ℂ) :=
    ⟨radius + ‖center time‖ + 2, radius + ‖center time‖ + 3,
      by positivity, by linarith⟩
  let test : ℂ → ℂ := fun argument => (cutoff argument : ℂ) *
    Section6.smoothConjugateInversePower distance (power + 1) argument
  have smooth : ContDiff ℝ ∞ test :=
    (Complex.ofRealCLM.contDiff.comp cutoff.contDiff).mul
      (Section6.smoothConjugateInversePower_contDiff distancePositive _)
  have compact : HasCompactSupport test :=
    (cutoff.hasCompactSupport.comp_left (g := fun value : ℝ => (value : ℂ)) (by simp)).mul_right
  have centerSmall : ∀ᶠ current in 𝓝 time, ‖center current‖ < ‖center time‖ + 1 :=
    centerDerivative.continuousAt.norm.eventually (eventually_lt_nhds (by linarith : ‖center time‖ < ‖center time‖ + 1))
  have argumentsSmall (current : ℝ) (member : current ∈ Icc 0 horizon)
      (small : ‖center current‖ < ‖center time‖ + 1) (position : ℂ)
      (inDomain : position ∈ motion.domain current index patch) :
      center current - position ∈ Metric.ball (0 : ℂ) cutoff.rIn := by
    have positionBound : ‖position‖ ≤ radius := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using domains current member index patch inDomain
    simp only [Metric.mem_ball, dist_zero_right]
    change ‖center current - position‖ < radius + ‖center time‖ + 2
    have triangle := norm_sub_le (center current) position
    linarith only [triangle, positionBound, small]
  have result := evolution.hasDerivAt_patch_moving_smooth_transport_of_boundary_gaps
    horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch
    inside centerDerivative smooth compact
  have momentEquality :
      (fun current => ∫ position, patchDensity scales motion current index patch position •
        (star (center current - position))⁻¹ ^ (power + 1)) =ᶠ[𝓝 time]
      (fun current => ∫ position, patchDensity scales motion current index patch position •
        test (center current - position)) := by
    filter_upwards [Icc_mem_nhds inside.1 inside.2, centerSmall, separatedNear] with current member small gap
    apply integral_congr_ae
    apply Eventually.of_forall
    intro position
    by_cases inDomain : position ∈ motion.domain current index patch
    · have one := (cutoff.eventuallyEq_one_of_mem_ball (argumentsSmall current member small position inDomain)).self_of_nhds
      have kernel := (Section6.smoothConjugateInversePower_eventuallyEq distancePositive (power + 1)
        (gap position inDomain)).self_of_nhds
      change patchDensity scales motion current index patch position • _ =
        patchDensity scales motion current index patch position • _
      simp only [test, one, Pi.one_apply, Complex.ofReal_one, one_mul, kernel]
    · simp only [patchDensity, indicator_of_not_mem inDomain, zero_smul]
  have actual := result.congr_of_eventuallyEq momentEquality
  convert actual using 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro position
  by_cases inDomain : position ∈ motion.domain time index patch
  · have localEquality : test =ᶠ[𝓝 (center time - position)]
        Section6.smoothConjugateInversePower distance (power + 1) := by
      filter_upwards [cutoff.eventuallyEq_one_of_mem_ball
        (argumentsSmall time ⟨inside.1.le, inside.2.le⟩ (by linarith) position inDomain)] with argument one
      simp only [test, one, Pi.one_apply, Complex.ofReal_one, one_mul]
    have derivative := (Section6.smoothConjugateInversePower_hasFDerivAt distancePositive power
      (separatedNear.self_of_nhds position inDomain)).congr_of_eventuallyEq localEquality
    change -((power + 1 : ℕ) : ℂ) * (patchDensity scales motion time index patch position • _) =
      patchDensity scales motion time index patch position •
        (fderiv ℝ test (center time - position)) _
    rw [derivative.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, starRingEnd_apply, Complex.real_smul, smul_eq_mul]
    ring
  · simp only [patchDensity, indicator_of_not_mem inDomain, zero_smul, mul_zero]

end EulerNonuniqueness.Paper
