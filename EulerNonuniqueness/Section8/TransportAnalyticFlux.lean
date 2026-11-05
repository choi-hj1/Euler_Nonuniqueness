import EulerNonuniqueness.General.VariableLinearLp
import EulerNonuniqueness.Section8.TransportAnalyticDecay

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.continuous_transportFlux
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    {test : Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Continuous (fun time : Icc (0 : ℝ) horizon => ∫ position,
      omega time position * fderiv ℝ test position (biotSavart (omega time) position)) := by
  obtain ⟨operatorBound, operatorBounded⟩ :=
    (compact.fderiv ℝ).exists_bound_of_continuous (smooth.continuous_fderiv (by simp))
  obtain ⟨bound, finite, bounded⟩ := hypotheses.uniformBounds 2 (by norm_num)
  obtain ⟨exponentBound, velocityMembers, velocityContinuous⟩ := hypotheses.continuousInLp_biotSavart
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨exponentBound⟩
  have testMembers (time : Icc (0 : ℝ) horizon) : MemLp
      (fun position => fderiv ℝ test position (biotSavart (omega time) position)) 2 volume :=
    (velocityMembers time).apply_bounded_continuousLinearMap
      (smooth.continuous_fderiv (by simp)).aestronglyMeasurable operatorBounded
  apply continuous_iff_continuousAt.mpr
  intro time
  have velocityConverges : Tendsto
      (fun other : Icc (0 : ℝ) horizon => eLpNorm (biotSavart (omega other) - biotSavart (omega time)) 2 volume)
      (𝓝 time) (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun other : Icc (0 : ℝ) horizon => biotSavart (omega other))
      velocityMembers (biotSavart (omega time)) (velocityMembers time)).mp (velocityContinuous.tendsto time)
  apply tendsto_integral_mul_of_weakL2_strongL2
    (sequence := fun other : Icc (0 : ℝ) horizon => omega other) (limit := omega time)
    (fun other : Icc (0 : ℝ) horizon => hypotheses.weakL2Continuous.1 other other.property)
    testMembers (testMembers time) (bound := bound.toReal)
  · intro other
    exact ENNReal.toReal_mono finite.ne (by simpa using bounded other other.property)
  · intro fixedTest member
    exact (hypotheses.weakL2Continuous.2 fixedTest member).tendsto time
  · exact tendsto_eLpNorm_apply_bounded_continuousLinearMap_sub operatorBounded velocityConverges

theorem TransportAnalyticHypotheses.integrable_transportFlux
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun position => omega time position * fderiv ℝ test position (biotSavart (omega time) position)) := by
  obtain ⟨bound, bounded⟩ := (compact.fderiv ℝ).exists_bound_of_continuous (smooth.continuous_fderiv (by simp))
  have productMember : MemLp
      ((fun position => fderiv ℝ test position (biotSavart (omega time) position)) * omega time) 1 volume :=
    (hypotheses.weakL2Continuous.1 time inside).mul
      ((hypotheses.biotSavart_memLp_two inside).apply_bounded_continuousLinearMap
        (smooth.continuous_fderiv (by simp)).aestronglyMeasurable bounded)
  simpa only [Pi.mul_apply, mul_comm] using memLp_one_iff_integrable.mp productMember

theorem TransportAnalyticHypotheses.integrable_smooth_moment
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun position => omega time position * test position) := by
  have testMember : MemLp test 2 volume := smooth.continuous.memLp_of_hasCompactSupport compact
  have productMember : MemLp (test * omega time) 1 volume := (hypotheses.weakL2Continuous.1 time inside).mul testMember
  have integrable := memLp_one_iff_integrable.mp productMember
  change Integrable (fun position => test position * omega time position) at integrable
  simpa only [mul_comm] using integrable

end EulerNonuniqueness
