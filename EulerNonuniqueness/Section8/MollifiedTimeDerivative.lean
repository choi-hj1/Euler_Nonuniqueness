import EulerNonuniqueness.General.DerivativeFromIntervalFTC
import EulerNonuniqueness.Section8.TimeCommutator
import EulerNonuniqueness.Section8.TimeTransport

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff Convolution

namespace EulerNonuniqueness

set_option maxHeartbeats 1000000

theorem mollification_eq_source_moment (vorticity : Vorticity) (index : ℕ) (position : Plane) :
    mollification vorticity index position =
      ∫ source, vorticity source * (mollifierBump index).normed volume (position - source) := by
  have equality := integral_sub_left_eq_self
    (fun offset => (mollifierBump index).normed volume offset * vorticity (position - offset)) volume position
  simpa only [mollification, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
    sub_sub_cancel, mul_comm] using equality.symm

theorem LocalCompactnessHypotheses.hasDerivAt_smooth_moment
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonPositive : 0 < horizon) (index : ℕ) {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    {time : ℝ} (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun other => ∫ source, sequence index other source * test source)
      (∫ source, sequence index time source * fderiv ℝ test source
        (biotSavart (sequence index time) source)) time := by
  have sourceContinuous : ContinuousOn (fun other => ∫ source, sequence index other source *
      fderiv ℝ test source (biotSavart (sequence index other) source)) (Icc 0 horizon) :=
    continuousOn_iff_continuous_restrict.mpr
      (hypotheses.continuous_transportFlux horizonPositive.le index smooth compact)
  exact hasDerivAt_of_sub_eq_intervalIntegral_on_Icc
    (function := fun other => ∫ source, sequence index other source * test source)
    sourceContinuous horizonPositive
    (fun other otherInside => hypotheses.smooth_moment_sub_eq_intervalIntegral horizonPositive index
      smooth compact (first := 0) (second := other) ⟨le_rfl, horizonPositive.le⟩ otherInside) inside

theorem LocalCompactnessHypotheses.hasDerivAt_mollification
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonPositive : 0 < horizon) (index mollifierIndex : ℕ) (position : Plane)
    {time : ℝ} (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun other => mollification (sequence index other) mollifierIndex position)
      (transportCommutator ((mollifierBump mollifierIndex).normed volume)
          (biotSavart (sequence index time)) (sequence index time) position -
        fderiv ℝ (mollification (sequence index time) mollifierIndex) position
          (biotSavart (sequence index time) position)) time := by
  let kernel := (mollifierBump (Space := Plane) mollifierIndex).normed (volume : Measure Plane)
  have smooth : ContDiff ℝ ∞ kernel := (mollifierBump mollifierIndex).contDiff_normed
  have compact : HasCompactSupport kernel := (mollifierBump mollifierIndex).hasCompactSupport_normed
  have reflectedSmooth : ContDiff ℝ ∞ (fun source => kernel (position - source)) :=
    smooth.comp (contDiff_const.sub contDiff_id)
  have reflectedCompact : HasCompactSupport (fun source => kernel (position - source)) :=
    compact.comp_homeomorph (Homeomorph.subLeft position)
  have derivative := hypotheses.hasDerivAt_smooth_moment horizonPositive index reflectedSmooth reflectedCompact inside
  have momentEquality : (fun other => ∫ source, sequence index other source * kernel (position - source)) =
      (fun other => mollification (sequence index other) mollifierIndex position) := by
    funext other
    exact (mollification_eq_source_moment (sequence index other) mollifierIndex position).symm
  rw [momentEquality] at derivative
  convert derivative using 1
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.2.1
  have timeInside : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
  have members := fun exponent bound => ((hypotheses.2.2 index).2.2.2 exponent bound time timeInside).1
  have integrable : Integrable (sequence index time) :=
    memLp_one_iff_integrable.mp (by simpa using members 1 le_rfl)
  rw [transportCommutator_eq_mollifiedTransport integrable
    (integrable_vorticity_smul_biotSavart radiusPositive.le members (supported index time timeInside)
      ((hypotheses.2.2 index).2.2.1 time timeInside).2) smooth compact]
  have equality := integral_sub_left_eq_self
    (fun offset => sequence index time (position - offset) * fderiv ℝ kernel offset
      (biotSavart (sequence index time) (position - offset))) volume position
  simp only [sub_sub_cancel] at equality
  simp_rw [fderiv_reflected_test smooth, ContinuousLinearMap.neg_apply, mul_neg]
  rw [integral_neg, equality]
  change _ - _ - fderiv ℝ (kernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] sequence index time) position
    (biotSavart (sequence index time) position) = _
  ring

end EulerNonuniqueness
