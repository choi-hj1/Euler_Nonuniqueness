import EulerNonuniqueness.Section8.TransportAnalyticTime
import EulerNonuniqueness.Section8.MollifiedTransport
import EulerNonuniqueness.Section8.TimeCommutator

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff Convolution

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.continuous_mollifiedDerivative_time
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel)
    (position direction : Plane) :
    Continuous (fun time : Icc (0 : ℝ) horizon =>
      fderiv ℝ (kernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] omega time) position direction) := by
  have testSmooth : ContDiff ℝ ∞ (fun point => fderiv ℝ kernel (position - point) direction) :=
    (contDiff_directionalDerivative smooth direction).comp (contDiff_const.sub contDiff_id)
  have testCompact : HasCompactSupport (fun point => fderiv ℝ kernel (position - point) direction) :=
    (compact.fderiv_apply ℝ direction).comp_homeomorph (Homeomorph.subLeft position)
  have result := hypotheses.weakL2Continuous.2 _ (testSmooth.continuous.memLp_of_hasCompactSupport testCompact)
  convert result using 1
  funext time
  exact fderiv_scalarConvolution_apply_source (hypotheses.integrable time.property) smooth compact position direction

theorem TransportAnalyticHypotheses.continuous_transportCommutator_time
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel)
    (position : Plane) :
    Continuous (fun time : Icc (0 : ℝ) horizon =>
      transportCommutator kernel (biotSavart (omega time)) (omega time) position) := by
  have reflectedSmooth : ContDiff ℝ ∞ (fun point => kernel (position - point)) :=
    smooth.comp (contDiff_const.sub contDiff_id)
  have reflectedCompact : HasCompactSupport (fun point => kernel (position - point)) :=
    compact.comp_homeomorph (Homeomorph.subLeft position)
  have fluxContinuous := hypotheses.continuous_transportFlux reflectedSmooth reflectedCompact
  have velocityContinuous := hypotheses.continuous_biotSavart_time position
  have firstContinuous :=
    (((Complex.continuous_re.comp velocityContinuous).mul
      (hypotheses.continuous_mollifiedDerivative_time smooth compact position 1)).add
      ((Complex.continuous_im.comp velocityContinuous).mul
        (hypotheses.continuous_mollifiedDerivative_time smooth compact position Complex.I)))
  convert firstContinuous.add fluxContinuous using 1
  funext time
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.supported
  rw [transportCommutator_eq_mollifiedTransport (hypotheses.integrable time.property)
    (integrable_vorticity_smul_biotSavart radiusPositive.le
      (fun exponent bound => hypotheses.membership exponent bound time time.property)
      (supported time time.property) (hypotheses.zeroMean time time.property)) smooth compact]
  rw [realLinearMap_apply_complex]
  have changeVariables := integral_sub_left_eq_self
    (fun offset => omega time (position - offset) * fderiv ℝ kernel offset
      (biotSavart (omega time) (position - offset))) volume position
  simp only [sub_sub_cancel] at changeVariables
  rw [← changeVariables]
  simp_rw [fderiv_reflected_test smooth, ContinuousLinearMap.neg_apply, mul_neg]
  rw [integral_neg]
  simp only [Function.comp_apply]
  ring

theorem TransportAnalyticHypotheses.measurable_transportCommutator
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel) :
    Measurable (fun point : Icc (0 : ℝ) horizon × Plane =>
      transportCommutator kernel (biotSavart (omega point.1)) (omega point.1) point.2) := by
  have spatialContinuous (time : Icc (0 : ℝ) horizon) :
      Continuous (transportCommutator kernel (biotSavart (omega time)) (omega time)) := by
    obtain ⟨radius, positive, supported⟩ := hypotheses.supported
    exact continuous_transportCommutator (hypotheses.integrable time.property)
      (integrable_vorticity_smul_biotSavart positive.le
        (fun exponent bound => hypotheses.membership exponent bound time time.property)
        (supported time time.property) (hypotheses.zeroMean time time.property))
      (hypotheses.continuous_biotSavart time.property) smooth compact
  exact (measurable_uncurry_of_continuous_of_measurable spatialContinuous
    (fun position => (hypotheses.continuous_transportCommutator_time smooth compact position).measurable)).comp measurable_swap

theorem TransportAnalyticHypotheses.uniform_integral_transportCommutator_mollifier_norm
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ mollifierIndex (time : Icc (0 : ℝ) horizon),
      Integrable (transportCommutator ((mollifierBump mollifierIndex).normed volume)
        (biotSavart (omega time)) (omega time)) ∧
      (∫ position, ‖transportCommutator ((mollifierBump mollifierIndex).normed volume)
        (biotSavart (omega time)) (omega time) position‖) ≤ bound := by
  obtain ⟨radius, positive, supported⟩ := hypotheses.supported
  obtain ⟨normBound, finite, bounded⟩ := hypotheses.uniformBounds 2 (by norm_num)
  let moment : ℝ := ∫ offset : Plane, ‖fderiv ℝ ((mollifierBump 0).normed volume) offset‖ * ‖offset‖
  have momentNonnegative : 0 ≤ moment := integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨moment * (2 * normBound.toReal ^ 2), by positivity, ?_⟩
  intro mollifierIndex time
  have result := integral_transportCommutator_mollifier_norm_le positive.le
    (fun exponent bound => hypotheses.membership exponent bound time time.property)
    (supported time time.property) (hypotheses.zeroMean time time.property) mollifierIndex
  refine ⟨result.1, result.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ momentNonnegative
  have sourceBound : (eLpNorm (omega time) 2 volume).toReal ≤ normBound.toReal :=
    ENNReal.toReal_mono finite.ne (by simpa using bounded time time.property)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg sourceBound 2) (by norm_num)

end EulerNonuniqueness
