import EulerNonuniqueness.Section8.SupportedPassiveMoments
import EulerNonuniqueness.General.ODEClosedIntervalDerivative

noncomputable section

open Set MeasureTheory Filter Function
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem WeakTransportOn.supported_passive_smooth_moment_closed_derivative
    {horizon : ℝ} {initial : Vorticity} {density : Evolution} {velocity : ℝ → Velocity}
    (transport : WeakTransportOn horizon initial density velocity)
    (densityContinuous : ContinuousInLpOn horizon 2 density)
    (velocityContinuous : ContinuousInLpOn horizon 2 velocity)
    (horizonPositive : 0 < horizon) {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (supported : ∀ current ∈ Icc 0 horizon, support (density current) ⊆ Metric.closedBall 0 radius)
    {test : Plane → ℝ} (smooth : ContDiff ℝ ∞ test) :
    ContinuousOn (fun current => ∫ position, density current position * test position) (Icc 0 horizon) ∧
    ContinuousOn (fun current => ∫ position, density current position * fderiv ℝ test position (velocity current position)) (Icc 0 horizon) ∧
    ∀ time ∈ Icc 0 horizon,
      HasDerivWithinAt (fun current => ∫ position, density current position * test position)
        (∫ position, density time position * fderiv ℝ test position (velocity time position)) (Icc 0 horizon) time := by
  let cutoff : ContDiffBump (0 : Plane) := ⟨radius + 1, radius + 2, by linarith, by linarith⟩
  let modified := fun position => cutoff position * test position
  have modifiedSmooth : ContDiff ℝ ∞ modified := cutoff.contDiff.mul smooth
  have modifiedCompact : HasCompactSupport modified := cutoff.hasCompactSupport.mul_right
  have sameGerm (position : Plane) (member : position ∈ Metric.closedBall (0 : Plane) radius) :
      modified =ᶠ[𝓝 position] test := by
    have near : position ∈ Metric.ball (0 : Plane) cutoff.rIn := by
      change dist position 0 < radius + 1
      change dist position 0 ≤ radius at member
      linarith only [member]
    filter_upwards [cutoff.eventuallyEq_one_of_mem_ball near] with other one
    simp only [modified, one, one_mul, Pi.one_apply]
  have momentEquality (current : ℝ) (member : current ∈ Icc 0 horizon) :
      (∫ position, density current position * test position) = ∫ position, density current position * modified position := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro position
    by_cases zero : density current position = 0
    · simp only [zero, zero_mul]
    · change density current position * test position = density current position * modified position
      rw [(sameGerm position (supported current member zero)).self_of_nhds]
  have fluxEquality (current : ℝ) (member : current ∈ Icc 0 horizon) :
      (∫ position, density current position * fderiv ℝ modified position (velocity current position)) =
        ∫ position, density current position * fderiv ℝ test position (velocity current position) := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro position
    by_cases zero : density current position = 0
    · simp only [zero, zero_mul]
    · change density current position * fderiv ℝ modified position (velocity current position) =
        density current position * fderiv ℝ test position (velocity current position)
      rw [(sameGerm position (supported current member zero)).fderiv_eq]
  have testMember : MemLp modified 2 volume := modifiedSmooth.continuous.memLp_of_hasCompactSupport modifiedCompact
  have modifiedMomentContinuous : ContinuousOn (fun current => ∫ position, density current position * modified position) (Icc 0 horizon) :=
    continuousOn_iff_continuous_restrict.mpr (densityContinuous.weakL2ContinuousOn.2 modified testMember)
  have momentContinuous : ContinuousOn (fun current => ∫ position, density current position * test position) (Icc 0 horizon) := by
    apply modifiedMomentContinuous.congr
    intro current member
    exact momentEquality current member
  have modifiedFluxContinuous := densityContinuous.continuousOn_passiveTransportFlux velocityContinuous modifiedSmooth modifiedCompact
  have fluxContinuous : ContinuousOn (fun current => ∫ position, density current position * fderiv ℝ test position (velocity current position)) (Icc 0 horizon) := by
    apply modifiedFluxContinuous.congr
    intro current member
    exact (fluxEquality current member).symm
  let flux : ℝ → ℝ := fun current => ∫ position, density current position * fderiv ℝ test position (velocity current position)
  let extension : ℝ → ℝ := fun current => flux (projIcc 0 horizon horizonPositive.le current)
  have extensionContinuous : Continuous extension :=
    (continuousOn_iff_continuous_restrict.mp fluxContinuous).comp continuous_projIcc
  have agreement (current : ℝ) (member : current ∈ Icc 0 horizon) : extension current = flux current := by
    simp only [extension, projIcc_of_mem horizonPositive.le member]
  have interiorEquation (current : ℝ) (member : current ∈ Ioo 0 horizon) :
      HasDerivAt (fun other => ∫ position, density other position * test position) (extension current) current := by
    rw [agreement current ⟨member.1.le, member.2.le⟩]
    exact transport.hasDerivAt_supported_passive_smooth_moment densityContinuous velocityContinuous horizonPositive radiusNonnegative supported smooth member
  refine ⟨momentContinuous, fluxContinuous, ?_⟩
  intro time member
  have actual := hasDerivWithinAt_Icc_of_continuous_interior_derivative momentContinuous extensionContinuous interiorEquation time member
  rwa [agreement time member] at actual

end EulerNonuniqueness
