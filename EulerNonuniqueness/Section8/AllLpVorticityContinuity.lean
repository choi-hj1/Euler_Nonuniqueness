import EulerNonuniqueness.Section8.StrongVorticityContinuity
import EulerNonuniqueness.General.UniformLpIntegrability

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.continuousInLp_vorticity
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon)
    {exponent : ℝ} (exponentBound : 1 ≤ exponent) :
    ContinuousInLpOn horizon (ENNReal.ofReal exponent) omega := by
  have lpBound : 1 ≤ ENNReal.ofReal exponent := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal exponentBound
  letI : Fact (1 ≤ ENNReal.ofReal exponent) := ⟨lpBound⟩
  let members := fun time : Icc (0 : ℝ) horizon => hypotheses.membership exponent exponentBound time time.property
  refine ⟨lpBound, members, ?_⟩
  apply continuous_iff_seqContinuous.mpr
  intro times time converges
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun step => members (times step)) _ (members time)).mpr
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.supported
  let region := Metric.closedBall (0 : Plane) radius
  let measure := volume.restrict region
  letI : IsFiniteMeasure measure := ⟨by
    simpa only [measure, Measure.restrict_apply_univ] using (isCompact_closedBall (0 : Plane) radius).measure_lt_top⟩
  obtain ⟨twoBound, twoMembers, twoContinuous⟩ := hypotheses.continuousInLp_vorticity_two positive
  have l2Convergence := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _
    (fun step => twoMembers (times step)) _ (twoMembers time)).mp ((twoContinuous.tendsto time).comp converges)
  have restrictedConvergence : Tendsto (fun step => eLpNorm (omega (times step) - omega time) 2 measure) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds l2Convergence
      (fun _ => zero_le _) (fun step => eLpNorm_restrict_le _ _ _ _)
  have inMeasure := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (fun step => (twoMembers (times step)).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
    ((twoMembers time).aestronglyMeasurable.mono_measure Measure.restrict_le_self) restrictedConvergence
  obtain ⟨higherBound, higherFinite, higherBounded⟩ := hypotheses.uniformBounds (exponent + 1) (by linarith)
  have higherEstimate (step : ℕ) : eLpNorm (omega (times step)) (ENNReal.ofReal (exponent + 1)) measure ≤
      ENNReal.ofReal higherBound.toReal := by
    rw [ENNReal.ofReal_toReal higherFinite.ne]
    exact (eLpNorm_restrict_le _ _ _ _).trans (higherBounded (times step) (times step).property)
  have measurable (step : ℕ) := (members (times step)).aestronglyMeasurable.mono_measure (show measure ≤ volume from Measure.restrict_le_self)
  have uniformlyIntegrable := unifIntegrable_of_uniform_higherLp (by positivity : 0 < ENNReal.ofReal exponent)
    (show ENNReal.ofReal exponent < ENNReal.ofReal (exponent + 1) from
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
    (by simp : ENNReal.ofReal (exponent + 1) ≠ ⊤) measurable ENNReal.toReal_nonneg higherEstimate
  have result := tendsto_Lp_finite_of_tendstoInMeasure lpBound (by simp) measurable
    ((members time).mono_measure (show measure ≤ volume from Measure.restrict_le_self)) uniformlyIntegrable inMeasure
  have differenceSupported (step : ℕ) : Function.support (omega (times step) - omega time) ⊆ region := by
    intro position nonzero
    by_contra outside
    have firstZero : omega (times step) position = 0 := by
      by_contra nonzero
      exact outside (supported (times step) (times step).property nonzero)
    have secondZero : omega time position = 0 := by
      by_contra nonzero
      exact outside (supported time time.property nonzero)
    exact nonzero (by simp only [Pi.sub_apply, firstZero, secondZero, sub_self])
  simpa only [measure, eLpNorm_restrict_eq_of_support_subset (differenceSupported _)] using result

end EulerNonuniqueness
