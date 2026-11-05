import EulerNonuniqueness.Section4.InitialReferenceShapeCoordinates
import EulerNonuniqueness.Section3.PatchStaticMoments
import EulerNonuniqueness.Section6.PatchSymmetricDifference

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.patchCentroid_eq_of_domain_eq_ball
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (patch : Fin 4) (center : ℂ)
    (radiusPositive : 0 < scales.radius (index.val + 1))
    (domainEquation : motion.domain time index patch = Metric.ball center (scales.radius (index.val + 1))) :
    patchCentroid motion time index patch = center := by
  have properties := evolution.2.2.2.1 time inside index patch
  have identityIntegrable : IntegrableOn (fun position : ℂ => position) (motion.domain time index patch) :=
    (continuous_id.continuousOn.integrableOn_compact properties.2.1.isCompact_closure).mono_set subset_closure
  have constantIntegrable : IntegrableOn (fun _ : ℂ => center) (motion.domain time index patch) :=
    (continuous_const.continuousOn.integrableOn_compact properties.2.1.isCompact_closure).mono_set subset_closure
  have moment := Section6.integral_ball_centered_identity center (scales.radius (index.val + 1))
  rw [← domainEquation, integral_sub identityIntegrable constantIntegrable, setIntegral_const] at moment
  have integralIdentity : (∫ position in motion.domain time index patch, position) =
      volume.real (motion.domain time index patch) • center := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using sub_eq_zero.mp moment
  have area : volume.real (motion.domain time index patch) = Real.pi * scales.radius (index.val + 1) ^ 2 := by
    rw [Measure.real, properties.2.2.1, ENNReal.toReal_ofReal (by positivity)]
  have areaPositive : 0 < volume.real (motion.domain time index patch) := by rw [area]; positivity
  rw [patchCentroid_eq_setAverage, average_eq, integralIdentity]
  simp only [Measure.real, Measure.restrict_apply_univ]
  change (volume.real (motion.domain time index patch))⁻¹ •
    (volume.real (motion.domain time index patch) • center) = center
  rw [smul_smul, inv_mul_cancel₀ areaPositive.ne', one_smul]

theorem FinitePatchEvolution.reference_initial_centroid
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon threshold : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonNonnegative : 0 ≤ horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) {phase unstable : Fin count → ℝ}
    (initial : ReferenceInitialDisks scales motion phase unstable threshold) (index : Fin count) (patch : Fin 4) :
    patchCentroid motion 0 index patch = initialDiskCenter scales (index.val + 1) (phase index) (unstable index) patch :=
  evolution.patchCentroid_eq_of_domain_eq_ball ⟨le_rfl, horizonNonnegative⟩ index patch _
    (scales.radius_pos amplitudePositive frequencyPositive ratioPositive _) ((initial index).2 patch).1

theorem FinitePatchEvolution.reference_initial_diagonals
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon threshold : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonNonnegative : 0 ≤ horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) {phase unstable : Fin count → ℝ}
    (initial : ReferenceInitialDisks scales motion phase unstable threshold) (index : Fin count) :
    positiveHalfDiagonal motion 0 index = initialPositiveDiagonal scales (index.val + 1) (phase index) (unstable index) ∧
    negativeHalfDiagonal motion 0 index = initialNegativeDiagonal scales (index.val + 1) (phase index) (unstable index) := by
  have centroid := evolution.reference_initial_centroid horizonNonnegative amplitudePositive frequencyPositive ratioPositive initial index
  constructor <;> simp only [positiveHalfDiagonal, negativeHalfDiagonal, centroid, initialDiskCenter,
    Fin.reduceEq, if_true, if_false] <;> ring

theorem FinitePatchEvolution.reference_initial_paper_shape
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon threshold : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonNonnegative : 0 ≤ horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) {phase unstable : Fin count → ℝ}
    (initial : ReferenceInitialDisks scales motion phase unstable threshold) (thresholdSmall : threshold ≤ 1 / 2)
    (index : Fin count) :
    0 < (negativeHalfDiagonal motion 0 index / positiveHalfDiagonal motion 0 index).im ∧
      (unstableShape motion 0 index, stableShape motion 0 index) = (unstable index, 0) := by
  have diagonals := evolution.reference_initial_diagonals horizonNonnegative amplitudePositive frequencyPositive ratioPositive initial index
  have raw := initialDiagonals_upper_and_shape scales (index.val + 1) (phase index) (unstable index)
    ((initial index).1.trans thresholdSmall)
  have upper : 0 < (negativeHalfDiagonal motion 0 index / positiveHalfDiagonal motion 0 index).im := by
    rw [diagonals.1, diagonals.2]
    exact raw.1
  refine ⟨upper, ?_⟩
  rw [← pointShapeChart_eq_paper_shape_of_upper motion 0 index upper, diagonals.1, diagonals.2]
  exact raw.2

end EulerNonuniqueness.Paper
