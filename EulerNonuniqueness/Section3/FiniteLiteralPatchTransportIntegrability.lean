import EulerNonuniqueness.Section3.FiniteLiteralPatchSpeed
import EulerNonuniqueness.Section8.RegularizedTransportIntegrability

open Set MeasureTheory
open scoped ENNReal ContDiff

namespace EulerNonuniqueness.Paper

noncomputable section

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem norm_vorticity_le_density_sum (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (position : ℂ) :
    ‖flow.vorticity time position‖ ≤ ∑ index, |configuration.density index| := by
  apply (flow.norm_vorticity_le_dominator time position).trans
  apply Finset.sum_le_sum
  intro index _
  by_cases member : position ∈ Metric.ball (configuration.center index) (2 * configuration.radius index)
  · simp only [indicator_of_mem member, mul_one, le_refl]
  · simp only [indicator_of_not_mem member, mul_zero]
    exact abs_nonneg _

theorem integrable_transport_terms (flow : FiniteLiteralPatchFlow configuration) (horizon : ℝ)
    {test : ℝ × ℂ → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun point : ℝ × ℂ => flow.vorticity point.1 point.2 *
      (timeDerivative test point + spatialDerivative test point (biotSavart (flow.vorticity point.1) point.2)))
      (spacetimeMeasure horizon) ∧
      Integrable (fun position => flow.vorticity 0 position * test (0, position)) := by
  obtain ⟨testBound, testBoundNonnegative, testBounded⟩ := scalarTest_uniform_bounds smooth compact
  obtain ⟨radius, _, outside⟩ := scalarTest_spatial_support compact
  have derivativeMeasurable := (smooth.continuous_fderiv (by simp)).aestronglyMeasurable
    (μ := spacetimeMeasure horizon)
  have temporalMeasurable : AEStronglyMeasurable (timeDerivative test) (spacetimeMeasure horizon) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (derivativeMeasurable.prodMk aestronglyMeasurable_const)
  have spatialMeasurable : AEStronglyMeasurable (fun point : ℝ × ℂ => spatialDerivative test point
      (biotSavart (flow.vorticity point.1) point.2)) (spacetimeMeasure horizon) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (derivativeMeasurable.prodMk (aestronglyMeasurable_const.prodMk flow.measurable_biotSavart_joint.aestronglyMeasurable))
  have coefficientMeasurable := temporalMeasurable.add spatialMeasurable
  have densityNonnegative : 0 ≤ ∑ index, |configuration.density index| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  constructor
  · apply integrable_spacetime_of_supported_bounded
      (flow.measurable_vorticity_joint.aestronglyMeasurable.mul coefficientMeasurable)
      (radius := radius)
      (bound := (∑ index, |configuration.density index|) * (testBound + testBound * flow.speedBound))
    · intro time _ position _
      have velocityEstimate := flow.norm_biotSavart_le_speedBound time position
      have coefficientEstimate : ‖timeDerivative test (time, position) + spatialDerivative test (time, position)
          (biotSavart (flow.vorticity time) position)‖ ≤ testBound + testBound * flow.speedBound :=
        (norm_add_le _ _).trans (add_le_add (testBounded time position).2.1
          (((testBounded time position).2.2 _).trans
            (mul_le_mul_of_nonneg_left velocityEstimate testBoundNonnegative)))
      simp only [Pi.mul_apply, Pi.add_apply]
      rw [norm_mul]
      exact mul_le_mul (flow.norm_vorticity_le_density_sum time position) coefficientEstimate
        (norm_nonneg _) densityNonnegative
    · intro time _ position notInside
      have vanishing := outside time position notInside
      simp only [Pi.mul_apply, Pi.add_apply, vanishing.2.1, vanishing.2.2, zero_add, mul_zero]
  · apply ((flow.vorticity_integrable 0).norm.mul_const testBound).mono'
      ((flow.vorticity_integrable 0).aestronglyMeasurable.mul
        (smooth.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun position => by
      simp only [Pi.mul_apply, Function.comp_apply, id_eq]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (testBounded 0 position).1 (norm_nonneg _)

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
