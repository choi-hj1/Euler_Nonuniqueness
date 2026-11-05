import EulerNonuniqueness.Section3.PolarIntegration

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

theorem integral_ball_polar {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    [CompleteSpace Value] {radius : ℝ} (radiusPositive : 0 < radius)
    (function : ℂ → Value) (continuous : ContinuousOn function (Metric.closedBall 0 radius)) :
    (∫ position in Metric.ball (0 : ℂ) radius, function position) =
      ∫ radial in Ioo (0 : ℝ) radius, ∫ angle in Ioo (-Real.pi) Real.pi,
        radial • function ((radial : ℂ) * standardCircle angle) := by
  have polarContinuous : Continuous (fun parameter : ℝ × ℝ =>
      (parameter.1 : ℂ) * standardCircle parameter.2) :=
    (Complex.continuous_ofReal.comp continuous_fst).mul
      (standardCircleBanach.val.1.continuous.comp continuous_snd)
  have maps : MapsTo (fun parameter : ℝ × ℝ => (parameter.1 : ℂ) * standardCircle parameter.2)
      (Icc (0 : ℝ) radius ×ˢ Icc (-Real.pi) Real.pi) (Metric.closedBall 0 radius) := by
    intro parameter member
    simpa [Metric.mem_closedBall, dist_zero_right, norm_mul, standardCircle_norm,
      abs_of_nonneg member.1.1] using member.1.2
  have jointContinuous : ContinuousOn (polarJacobianIntegrand function)
      (Icc (0 : ℝ) radius ×ˢ Icc (-Real.pi) Real.pi) :=
    continuous_fst.continuousOn.smul (continuous.comp polarContinuous.continuousOn maps)
  have joint : IntegrableOn (polarJacobianIntegrand function)
      (Ioo (0 : ℝ) radius ×ˢ Ioo (-Real.pi) Real.pi) (volume.prod volume) :=
    (jointContinuous.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have ballIdentity : polarInterior (fun _ => radius) = Metric.ball (0 : ℂ) radius := by
    ext position
    simp [polarInterior, Metric.mem_ball, dist_zero_right]
  have subgraphIdentity : polarSubgraph (fun _ => radius) =
      Ioo (0 : ℝ) radius ×ˢ Ioo (-Real.pi) Real.pi := by
    ext parameter
    simp [polarSubgraph, and_assoc]
  have transfer := integral_polarInterior_eq_subgraph (fun _ => radius) continuous_const
    (fun _ => rfl) radiusPositive (fun _ => le_rfl) function
  rw [ballIdentity, subgraphIdentity, Measure.volume_eq_prod] at transfer
  rw [IntegrableOn, ← Measure.prod_restrict] at joint
  rw [transfer, ← Measure.prod_restrict]
  exact integral_prod _ joint

end EulerNonuniqueness.Section6
