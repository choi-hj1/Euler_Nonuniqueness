import EulerNonuniqueness.Section8.TransportAnalyticInitialTrace

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem WeakTransportOn.initial_locallyIntegrable
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution} {velocity : ℝ → Velocity}
    (transport : WeakTransportOn horizon initial omega velocity) (positive : 0 < horizon) :
    LocallyIntegrable initial volume := by
  let temporal : ContDiffBump (0 : ℝ) := ⟨horizon / 4, horizon / 2, by positivity, by linarith⟩
  have temporalAtZero : temporal 0 = 1 := temporal.one_of_mem_closedBall (by simp [temporal]; positivity)
  intro center
  let spatial : ContDiffBump center := ⟨1, 2, by norm_num, by norm_num⟩
  let test : ℝ × Plane → ℝ := fun point => temporal point.1 * spatial point.2
  have admissible : ScalarTestOn horizon test := by
    refine ⟨(temporal.contDiff.comp contDiff_fst).mul (spatial.contDiff.comp contDiff_snd), ?_, ?_⟩
    · exact (temporal.hasCompactSupport.isCompact.prod spatial.hasCompactSupport.isCompact).of_isClosed_subset
        (isClosed_tsupport _) tsupport_separableTest_subset
    · intro time position after
      have temporalZero : temporal time = 0 := by
        apply temporal.zero_of_le_dist
        have nonnegative : 0 ≤ time := positive.le.trans after
        simp only [Real.dist_eq, sub_zero, abs_of_nonneg nonnegative]
        change horizon / 2 ≤ time
        linarith
      simp only [test, temporalZero, zero_mul]
  have initialIntegrable := (transport test admissible).2.1
  change Integrable (fun position => initial position * (temporal 0 * spatial position)) at initialIntegrable
  simp only [temporalAtZero, one_mul] at initialIntegrable
  refine ⟨Metric.ball center 1, Metric.ball_mem_nhds center (by norm_num), ?_⟩
  apply (initialIntegrable.restrict (s := Metric.ball center 1)).congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with position inside
  have spatialOne : spatial position = 1 := spatial.one_of_mem_closedBall (by
    exact Metric.ball_subset_closedBall inside)
  simp only [spatialOne, mul_one]

theorem TransportAnalyticHypotheses.initial_ae_eq
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon) :
    omega 0 =ᵐ[volume] initial := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (hypotheses.integrable ⟨le_rfl, positive.le⟩).locallyIntegrable
    (hypotheses.weakTransport.initial_locallyIntegrable positive)
  intro test smooth compact
  simpa only [smul_eq_mul, mul_comm] using hypotheses.initial_smooth_moment positive smooth compact

end EulerNonuniqueness
