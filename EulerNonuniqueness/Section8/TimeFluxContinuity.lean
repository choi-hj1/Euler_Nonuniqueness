import EulerNonuniqueness.General.VariableLinearLp
import EulerNonuniqueness.Section8.WeakVelocityContinuity

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem LocalCompactnessHypotheses.continuous_transportFlux
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) (index : ℕ) {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Continuous (fun time : Icc (0 : ℝ) horizon => ∫ position,
      sequence index time position *
        fderiv ℝ test position (biotSavart (sequence index time) position)) := by
  obtain ⟨operatorBound, operatorBounded⟩ :=
    (compact.fderiv ℝ).exists_bound_of_continuous (smooth.continuous_fderiv (by simp))
  obtain ⟨normBound, normBoundFinite, normBounded⟩ :=
    hypotheses.uniform_eLpNorm_bound horizonNonnegative (by norm_num : (1 : ℝ) ≤ 2)
  obtain ⟨exponentBound, velocityMembers, velocityContinuous⟩ :=
    hypotheses.continuousInLp_biotSavart horizonNonnegative index
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨exponentBound⟩
  have testMembers (time : Icc (0 : ℝ) horizon) : MemLp
      (fun position => fderiv ℝ test position (biotSavart (sequence index time) position))
      2 volume :=
    (velocityMembers time).apply_bounded_continuousLinearMap
      (smooth.continuous_fderiv (by simp)).aestronglyMeasurable operatorBounded
  apply continuous_iff_continuousAt.mpr
  intro time
  have velocityConverges : Tendsto
      (fun other : Icc (0 : ℝ) horizon =>
        eLpNorm (biotSavart (sequence index other) - biotSavart (sequence index time))
          2 volume) (𝓝 time) (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun other : Icc (0 : ℝ) horizon => biotSavart (sequence index other)) velocityMembers
      (biotSavart (sequence index time)) (velocityMembers time)).mp
        (velocityContinuous.tendsto time)
  apply tendsto_integral_mul_of_weakL2_strongL2
    (sequence := fun other : Icc (0 : ℝ) horizon => sequence index other)
    (limit := sequence index time)
    (fun other : Icc (0 : ℝ) horizon => (hypotheses.2.2 index).2.1.1 other other.property)
    testMembers (testMembers time) (bound := normBound.toReal)
  · intro other
    exact ENNReal.toReal_mono normBoundFinite.ne
      (by simpa using normBounded index other other.property)
  · intro fixedTest fixedMember
    exact ((hypotheses.2.2 index).2.1.2 fixedTest fixedMember).tendsto time
  · exact tendsto_eLpNorm_apply_bounded_continuousLinearMap_sub operatorBounded velocityConverges

theorem LocalCompactnessHypotheses.integrable_transportFlux
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (index : ℕ) {time : ℝ} (timeBound : time ∈ Icc 0 horizon) {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun position => sequence index time position *
      fderiv ℝ test position (biotSavart (sequence index time) position)) := by
  obtain ⟨bound, bounded⟩ :=
    (compact.fderiv ℝ).exists_bound_of_continuous (smooth.continuous_fderiv (by simp))
  have productMember : MemLp
      ((fun position => fderiv ℝ test position (biotSavart (sequence index time) position)) *
        sequence index time) 1 volume :=
    ((hypotheses.2.2 index).2.1.1 time timeBound).mul
      ((hypotheses.biotSavart_memLp_two index timeBound).apply_bounded_continuousLinearMap
        (smooth.continuous_fderiv (by simp)).aestronglyMeasurable bounded)
  simpa only [Pi.mul_apply, mul_comm] using memLp_one_iff_integrable.mp productMember

end EulerNonuniqueness
