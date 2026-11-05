import EulerNonuniqueness.Section8.PassiveTransportMoments

noncomputable section

open Set MeasureTheory Filter Function
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem WeakTransportOn.hasDerivAt_supported_passive_smooth_moment
    {horizon : ℝ} {initial : Vorticity} {density : Evolution} {velocity : ℝ → Velocity}
    (transport : WeakTransportOn horizon initial density velocity)
    (densityContinuous : ContinuousInLpOn horizon 2 density)
    (velocityContinuous : ContinuousInLpOn horizon 2 velocity)
    (horizonPositive : 0 < horizon) {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (supported : ∀ current ∈ Icc 0 horizon, support (density current) ⊆ Metric.closedBall 0 radius)
    {test : Plane → ℝ} (smooth : ContDiff ℝ ∞ test) {time : ℝ} (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun current => ∫ position, density current position * test position)
      (∫ position, density time position * fderiv ℝ test position (velocity time position)) time := by
  let cutoff : ContDiffBump (0 : Plane) := ⟨radius + 1, radius + 2, by linarith, by linarith⟩
  let modified := fun position => cutoff position * test position
  have modifiedSmooth : ContDiff ℝ ∞ modified := cutoff.contDiff.mul smooth
  have modifiedCompact : HasCompactSupport modified := cutoff.hasCompactSupport.mul_right
  have sameGerm (position : Plane) (member : position ∈ Metric.closedBall (0 : Plane) radius) :
      modified =ᶠ[𝓝 position] test := by
    have near : position ∈ Metric.ball (0 : Plane) cutoff.rIn := by
      change dist position 0 < radius + 1
      change dist position 0 ≤ radius at member
      linarith
    filter_upwards [cutoff.eventuallyEq_one_of_mem_ball near] with other one
    simp only [modified, one, one_mul, Pi.one_apply]
  have momentEquality (current : ℝ) (member : current ∈ Icc 0 horizon) :
      (∫ position, density current position * test position) =
        ∫ position, density current position * modified position := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro position
    by_cases zero : density current position = 0
    · simp only [zero, zero_mul]
    · change density current position * test position = density current position * modified position
      rw [(sameGerm position (supported current member zero)).self_of_nhds]
  have fluxEquality : (∫ position, density time position * fderiv ℝ modified position (velocity time position)) =
      ∫ position, density time position * fderiv ℝ test position (velocity time position) := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro position
    by_cases zero : density time position = 0
    · simp only [zero, zero_mul]
    · change density time position * fderiv ℝ modified position (velocity time position) =
        density time position * fderiv ℝ test position (velocity time position)
      have derivativeEquality : fderiv ℝ modified position = fderiv ℝ test position :=
        (sameGerm position (supported time ⟨inside.1.le, inside.2.le⟩ zero)).fderiv_eq
      rw [derivativeEquality]
  have derivative := transport.hasDerivAt_passive_smooth_moment densityContinuous velocityContinuous
    horizonPositive modifiedSmooth modifiedCompact inside
  rw [fluxEquality] at derivative
  apply derivative.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds inside.1 inside.2] with current member
  exact momentEquality current member

end EulerNonuniqueness
