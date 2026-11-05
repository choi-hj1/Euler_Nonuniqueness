import EulerNonuniqueness.General.ConvolutionContinuity
import EulerNonuniqueness.Section8.Compactness

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem continuous_biotSavart_of_memLp_support {vorticity : Vorticity}
    {exponent conjugate radius : ℝ}
    (conjugacy : exponent.HolderConjugate conjugate)
    (membership : MemLp vorticity (ENNReal.ofReal exponent) volume)
    (conjugateBound : conjugate < 2) (radiusNonnegative : 0 ≤ radius)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius) :
    Continuous (biotSavart vorticity) := by
  apply continuous_iff_continuousAt.mpr
  intro position
  let truncated := (Metric.ball 0 (‖position‖ + radius + 2)).indicator biotSavartKernel
  have kernelMember : MemLp truncated (ENNReal.ofReal conjugate) volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr
      (memLp_biotSavartKernel_ball conjugacy.symm.pos conjugateBound (by positivity))
  have continuousConvolution := continuous_convolution_smul_of_memLp conjugacy membership kernelMember
  have equalNear : biotSavart vorticity =ᶠ[𝓝 position]
      (fun other => ∫ source, vorticity source • truncated (other - source)) := by
    filter_upwards [Metric.ball_mem_nhds position (by norm_num : (0 : ℝ) < 1)] with other inside
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro source
    have near : ‖other‖ < ‖position‖ + 1 := by
      have triangle : ‖other‖ ≤ ‖other - position‖ + ‖position‖ := by
        simpa only [sub_add_cancel] using norm_add_le (other - position) position
      have distanceSmall : ‖other - position‖ < 1 := by
        simpa only [Metric.mem_ball, dist_eq_norm] using inside
      linarith
    exact (biotSavart_integrand_eq_truncated supportBound
      (show ‖other‖ + radius < ‖position‖ + radius + 2 by linarith) source).symm
  exact continuousConvolution.continuousAt.congr equalNear.symm

theorem equicontinuous_biotSavart_on_closedBall {Index : Type*}
    {vorticity : Index → Vorticity} {exponent conjugate radius observationRadius bound : ℝ}
    (conjugacy : exponent.HolderConjugate conjugate)
    (membership : ∀ index, MemLp (vorticity index) (ENNReal.ofReal exponent) volume)
    (conjugateBound : conjugate < 2) (radiusNonnegative : 0 ≤ radius)
    (observationNonnegative : 0 ≤ observationRadius)
    (supportBound : ∀ index, Function.support (vorticity index) ⊆ Metric.closedBall 0 radius)
    (normBound : ∀ index,
      (eLpNorm (vorticity index) (ENNReal.ofReal exponent) volume).toReal ≤ bound) :
    EquicontinuousOn (fun index => biotSavart (vorticity index))
      (Metric.closedBall 0 observationRadius) := by
  let truncated := (Metric.ball 0 (observationRadius + radius + 1)).indicator biotSavartKernel
  have kernelMember : MemLp truncated (ENNReal.ofReal conjugate) volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr
      (memLp_biotSavartKernel_ball conjugacy.symm.pos conjugateBound (by positivity))
  have convolutionEquicontinuous := equicontinuous_convolution_smul_of_memLp
    conjugacy membership kernelMember normBound
  have equalOn (index : Index) (position : Plane)
      (inside : position ∈ Metric.closedBall 0 observationRadius) :
      biotSavart (vorticity index) position =
        ∫ source, vorticity index source • truncated (position - source) := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro source
    have positionBound : ‖position‖ ≤ observationRadius := by simpa using inside
    exact (biotSavart_integrand_eq_truncated (supportBound index)
      (show ‖position‖ + radius < observationRadius + radius + 1 by linarith) source).symm
  intro position inside entourage entourageMember
  have near := (convolutionEquicontinuous position).equicontinuousWithinAt
    (Metric.closedBall 0 observationRadius) entourage entourageMember
  filter_upwards [near, self_mem_nhdsWithin] with other nearby otherInside index
  rw [equalOn index position inside, equalOn index other otherInside]
  exact nearby index

theorem LocalCompactnessHypotheses.equicontinuous_biotSavart_on_closedBall
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) {observationRadius : ℝ}
    (observationNonnegative : 0 ≤ observationRadius) :
    EquicontinuousOn
      (fun parameter : ℕ × Icc 0 horizon => biotSavart (sequence parameter.1 parameter.2))
      (Metric.closedBall 0 observationRadius) := by
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.2.1
  obtain ⟨bound, boundFinite, bounded⟩ :=
    hypotheses.uniform_eLpNorm_bound horizonNonnegative (by norm_num : (1 : ℝ) ≤ 4)
  apply EulerNonuniqueness.equicontinuous_biotSavart_on_closedBall
    (Index := ℕ × Icc (0 : ℝ) horizon)
    (vorticity := fun parameter => sequence parameter.1 parameter.2)
    (bound := bound.toReal) holderConjugate_four_fourThirds
    (fun parameter => ((hypotheses.2.2 parameter.1).2.2.2 4 (by norm_num)
      parameter.2 parameter.2.property).1) (by norm_num) radiusPositive.le observationNonnegative
    (fun parameter => supported parameter.1 parameter.2 parameter.2.property)
  intro parameter
  exact ENNReal.toReal_mono boundFinite.ne (bounded parameter.1 parameter.2 parameter.2.property)

end EulerNonuniqueness
