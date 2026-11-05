import EulerNonuniqueness.Section8.TransportAnalyticTime
import EulerNonuniqueness.Section8.MollifiedTimeDerivative

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff Convolution

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.hasDerivAt_mollification
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    (horizonPositive : 0 < horizon) (mollifierIndex : ℕ) (position : Plane)
    {time : ℝ} (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun other => mollification (omega other) mollifierIndex position)
      (transportCommutator ((mollifierBump mollifierIndex).normed volume) (biotSavart (omega time)) (omega time) position -
        fderiv ℝ (mollification (omega time) mollifierIndex) position (biotSavart (omega time) position)) time := by
  let kernel := (mollifierBump (Space := Plane) mollifierIndex).normed (volume : Measure Plane)
  have smooth : ContDiff ℝ ∞ kernel := (mollifierBump mollifierIndex).contDiff_normed
  have compact : HasCompactSupport kernel := (mollifierBump mollifierIndex).hasCompactSupport_normed
  have reflectedSmooth : ContDiff ℝ ∞ (fun source => kernel (position - source)) :=
    smooth.comp (contDiff_const.sub contDiff_id)
  have reflectedCompact : HasCompactSupport (fun source => kernel (position - source)) :=
    compact.comp_homeomorph (Homeomorph.subLeft position)
  have derivative := hypotheses.hasDerivAt_smooth_moment horizonPositive reflectedSmooth reflectedCompact inside
  have momentEquality : (fun other => ∫ source, omega other source * kernel (position - source)) =
      (fun other => mollification (omega other) mollifierIndex position) := by
    funext other
    exact (mollification_eq_source_moment (omega other) mollifierIndex position).symm
  rw [momentEquality] at derivative
  convert derivative using 1
  obtain ⟨radius, positive, supported⟩ := hypotheses.supported
  have timeInside : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
  rw [transportCommutator_eq_mollifiedTransport (hypotheses.integrable timeInside)
    (integrable_vorticity_smul_biotSavart positive.le
      (fun exponent bound => hypotheses.membership exponent bound time timeInside)
      (supported time timeInside) (hypotheses.zeroMean time timeInside)) smooth compact]
  have equality := integral_sub_left_eq_self
    (fun offset => omega time (position - offset) * fderiv ℝ kernel offset
      (biotSavart (omega time) (position - offset))) volume position
  simp only [sub_sub_cancel] at equality
  simp_rw [fderiv_reflected_test smooth, ContinuousLinearMap.neg_apply, mul_neg]
  rw [integral_neg, equality]
  change _ - _ - fderiv ℝ (kernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] omega time) position
    (biotSavart (omega time) position) = _
  ring

theorem TransportAnalyticHypotheses.hasDerivAt_renormalized_mollification
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    (horizonPositive : 0 < horizon) {renormalization : ℝ → ℝ}
    (smooth : ContDiff ℝ 1 renormalization) (mollifierIndex : ℕ) (position : Plane)
    {time : ℝ} (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun other => renormalization (mollification (omega other) mollifierIndex position))
      (deriv renormalization (mollification (omega time) mollifierIndex position) *
        (transportCommutator ((mollifierBump mollifierIndex).normed volume) (biotSavart (omega time)) (omega time) position -
          fderiv ℝ (mollification (omega time) mollifierIndex) position (biotSavart (omega time) position))) time :=
  ((smooth.differentiable (by simp) _).hasDerivAt).comp time
    (hypotheses.hasDerivAt_mollification horizonPositive mollifierIndex position inside)

end EulerNonuniqueness
