import EulerNonuniqueness.General.IntervalWeakDerivative
import EulerNonuniqueness.Section8.SeparableTransport
import EulerNonuniqueness.Section8.TimeFluxBounds

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem LocalCompactnessHypotheses.integrable_smooth_moment
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (index : ℕ) {time : ℝ} (timeBound : time ∈ Icc 0 horizon) {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun position => sequence index time position * test position) := by
  have testMember : MemLp test 2 volume := smooth.continuous.memLp_of_hasCompactSupport compact
  have productMember : MemLp (test * sequence index time) 1 volume :=
    ((hypotheses.2.2 index).2.1.1 time timeBound).mul testMember
  simpa only [Pi.mul_def, mul_comm] using memLp_one_iff_integrable.mp productMember

theorem LocalCompactnessHypotheses.uniform_smooth_moment_time_bound
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonPositive : 0 < horizon) {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ index, ∀ first ∈ Icc 0 horizon, ∀ second ∈ Icc 0 horizon,
      ‖(∫ position, sequence index second position * test position) -
        (∫ position, sequence index first position * test position)‖ ≤ bound * |second - first| := by
  obtain ⟨bound, boundNonnegative, bounded⟩ :=
    hypotheses.uniform_transportFlux_bound horizonPositive.le smooth compact
  refine ⟨bound, boundNonnegative, ?_⟩
  intro index first firstInside second secondInside
  have momentContinuous : ContinuousOn
      (fun time => ∫ position, sequence index time position * test position) (Icc 0 horizon) :=
    continuousOn_iff_continuous_restrict.mpr
      ((hypotheses.2.2 index).2.1.2 test (smooth.continuous.memLp_of_hasCompactSupport compact))
  have fluxContinuous : ContinuousOn (fun time => ∫ position, sequence index time position *
      fderiv ℝ test position (biotSavart (sequence index time) position)) (Icc 0 horizon) :=
    continuousOn_iff_continuous_restrict.mpr
      (hypotheses.continuous_transportFlux horizonPositive.le index smooth compact)
  refine momentContinuous.norm_sub_le_of_weak_derivative_setIntegral
    fluxContinuous horizonPositive ?_ (bounded index) firstInside secondInside
  intro temporal temporalSmooth temporalCompact temporalSupport
  exact ((hypotheses.2.2 index).1.separableTest_identity temporalSmooth temporalCompact temporalSupport
    smooth compact (fun time inside => hypotheses.integrable_smooth_moment index inside smooth compact)
    (fun time inside => hypotheses.integrable_transportFlux index inside smooth compact)).2

theorem LocalCompactnessHypotheses.smooth_moment_sub_eq_intervalIntegral
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonPositive : 0 < horizon) (index : ℕ) {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    {first second : ℝ} (firstInside : first ∈ Icc 0 horizon)
    (secondInside : second ∈ Icc 0 horizon) :
    (∫ position, sequence index second position * test position) -
      (∫ position, sequence index first position * test position) =
      ∫ time in first..second, ∫ position, sequence index time position *
        fderiv ℝ test position (biotSavart (sequence index time) position) := by
  have momentContinuous : ContinuousOn
      (fun time => ∫ position, sequence index time position * test position) (Icc 0 horizon) :=
    continuousOn_iff_continuous_restrict.mpr
      ((hypotheses.2.2 index).2.1.2 test (smooth.continuous.memLp_of_hasCompactSupport compact))
  have fluxContinuous : ContinuousOn (fun time => ∫ position, sequence index time position *
      fderiv ℝ test position (biotSavart (sequence index time) position)) (Icc 0 horizon) :=
    continuousOn_iff_continuous_restrict.mpr
      (hypotheses.continuous_transportFlux horizonPositive.le index smooth compact)
  refine momentContinuous.sub_eq_intervalIntegral_of_weak_derivative_setIntegral
    fluxContinuous horizonPositive ?_ firstInside secondInside
  intro temporal temporalSmooth temporalCompact temporalSupport
  exact ((hypotheses.2.2 index).1.separableTest_identity temporalSmooth temporalCompact temporalSupport
    smooth compact (fun time inside => hypotheses.integrable_smooth_moment index inside smooth compact)
    (fun time inside => hypotheses.integrable_transportFlux index inside smooth compact)).2

end EulerNonuniqueness
