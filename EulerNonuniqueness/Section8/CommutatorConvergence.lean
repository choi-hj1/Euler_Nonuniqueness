import EulerNonuniqueness.Section8.CommutatorEnvelope

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem aestronglyMeasurable_scaledCenteredTransportIntegrand
    {vorticity : Vorticity} {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (member : MemLp vorticity 4 volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel) (scale : ℝ) :
    AEStronglyMeasurable (fun point : Plane × Plane =>
      scaledCenteredTransportIntegrand kernel (biotSavart vorticity) vorticity scale point.2 point.1)
      ((volume : Measure Plane).prod volume) := by
  have velocityContinuous := continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds
    (by simpa using member) (by norm_num) radiusNonnegative supportBound
  have shifted := member.aestronglyMeasurable.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_scaled_sub scale)
  have original := member.aestronglyMeasurable.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_fst : QuasiMeasurePreserving (Prod.fst : Plane × Plane → Plane)
      ((volume : Measure Plane).prod volume) volume)
  have coefficient : Continuous (fun point : Plane × Plane => fderiv ℝ kernel point.2
      (scale⁻¹ • (biotSavart vorticity point.1 - biotSavart vorticity (point.1 - scale • point.2)))) :=
    ((smooth.continuous_fderiv (by simp)).comp continuous_snd).clm_apply
      (continuous_const.smul ((velocityContinuous.comp continuous_fst).sub
        (velocityContinuous.comp (continuous_fst.sub (continuous_const.smul continuous_snd)))))
  exact (shifted.sub original).mul coefficient.aestronglyMeasurable

theorem integral_scaledCenteredTransportIntegrand_norm_le_envelope
    {vorticity : Vorticity} {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (zeroMean : (∫ position, vorticity position) = 0)
    (kernel : Plane → ℝ) (scale : ℝ) (offset : Plane)
    (member : MemLp vorticity 2 volume) :
    (∫ position, ‖scaledCenteredTransportIntegrand kernel (biotSavart vorticity) vorticity scale offset position‖) ≤
      commutatorEnvelope kernel member scale offset := by
  have estimate := (integral_scaledCenteredTransportIntegrand_norm_le radiusNonnegative membership
    supportBound zeroMean kernel scale offset).2
  simpa only [commutatorEnvelope, Lp.norm_toLp, norm_translationLp_toLp_sub] using estimate

theorem integrable_scaledCenteredTransportIntegrand
    {vorticity : Vorticity} {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (zeroMean : (∫ position, vorticity position) = 0)
    {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel)
    (scale : ℝ) :
    Integrable (fun point : Plane × Plane =>
      scaledCenteredTransportIntegrand kernel (biotSavart vorticity) vorticity scale point.2 point.1)
      ((volume : Measure Plane).prod volume) := by
  have member : MemLp vorticity 2 volume := by simpa using membership 2 (by norm_num)
  have measurable := aestronglyMeasurable_scaledCenteredTransportIntegrand radiusNonnegative
    (by simpa using membership 4 (by norm_num)) supportBound smooth scale
  apply (integrable_prod_iff' measurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun offset =>
      (integral_scaledCenteredTransportIntegrand_norm_le radiusNonnegative membership
        supportBound zeroMean kernel scale offset).1
  · apply ((continuous_commutatorEnvelope smooth member scale).integrable_of_hasCompactSupport
      (hasCompactSupport_commutatorEnvelope compact member scale)).mono'
      measurable.prod_swap.norm.integral_prod_right'
    filter_upwards [] with offset
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact integral_scaledCenteredTransportIntegrand_norm_le_envelope radiusNonnegative membership
      supportBound zeroMean kernel scale offset member

def scaledCenteredTransportCommutator (kernel : Plane → ℝ) (velocity : Velocity)
    (vorticity : Vorticity) (scale : ℝ) (position : Plane) : ℝ :=
  ∫ offset, scaledCenteredTransportIntegrand kernel velocity vorticity scale offset position

theorem integral_scaledCenteredTransportCommutator_norm_le
    {vorticity : Vorticity} {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (zeroMean : (∫ position, vorticity position) = 0)
    {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel)
    (scale : ℝ) (member : MemLp vorticity 2 volume) :
    Integrable (scaledCenteredTransportCommutator kernel (biotSavart vorticity) vorticity scale) ∧
      (∫ position, ‖scaledCenteredTransportCommutator kernel (biotSavart vorticity) vorticity scale position‖) ≤
        ∫ offset, commutatorEnvelope kernel member scale offset := by
  have joint := integrable_scaledCenteredTransportIntegrand radiusNonnegative membership
    supportBound zeroMean smooth compact scale
  refine ⟨joint.integral_prod_left, ?_⟩
  calc
    _ ≤ ∫ position, ∫ offset,
        ‖scaledCenteredTransportIntegrand kernel (biotSavart vorticity) vorticity scale offset position‖ :=
      integral_mono joint.integral_prod_left.norm joint.integral_norm_prod_left
        (fun _ => norm_integral_le_integral_norm _)
    _ = ∫ offset, ∫ position,
        ‖scaledCenteredTransportIntegrand kernel (biotSavart vorticity) vorticity scale offset position‖ :=
      integral_integral_swap joint.norm
    _ ≤ ∫ offset, commutatorEnvelope kernel member scale offset :=
      integral_mono joint.norm.integral_prod_right
        ((continuous_commutatorEnvelope smooth member scale).integrable_of_hasCompactSupport
          (hasCompactSupport_commutatorEnvelope compact member scale))
        (fun offset => integral_scaledCenteredTransportIntegrand_norm_le_envelope radiusNonnegative
          membership supportBound zeroMean kernel scale offset member)

theorem tendsto_integral_scaledCenteredTransportCommutator_norm
    {vorticity : Vorticity} {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (zeroMean : (∫ position, vorticity position) = 0)
    {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel)
    {scales : ℕ → ℝ} (scalesConverge : Tendsto scales atTop (𝓝 0)) :
    Tendsto (fun index => ∫ position,
      ‖scaledCenteredTransportCommutator kernel (biotSavart vorticity) vorticity (scales index) position‖)
      atTop (𝓝 0) := by
  have member : MemLp vorticity 2 volume := by simpa using membership 2 (by norm_num)
  exact squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun index => (integral_scaledCenteredTransportCommutator_norm_le radiusNonnegative membership
      supportBound zeroMean smooth compact (scales index) member).2)
    (tendsto_integral_commutatorEnvelope smooth compact member scalesConverge)

end EulerNonuniqueness
