import EulerNonuniqueness.Section8.RegularizedMeasurability
import EulerNonuniqueness.Section8.RegularizedBounds
import EulerNonuniqueness.Section8.TestBounds

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.renormalized_mollification_integrable_terms
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (nonnegative : 0 ≤ horizon)
    {renormalization : ℝ → ℝ} (smooth : ContDiff ℝ 1 renormalization)
    {test : ℝ × Plane → ℝ} (testSmooth : ContDiff ℝ ∞ test) (testCompact : HasCompactSupport test)
    (index : ℕ) :
    Integrable (fun point : ℝ × Plane => renormalization (mollification (omega point.1) index point.2) *
      timeDerivative test point) (spacetimeMeasure horizon) ∧
    Integrable (fun point : ℝ × Plane => renormalization (mollification (omega point.1) index point.2) *
      spatialDerivative test point (biotSavart (omega point.1) point.2)) (spacetimeMeasure horizon) ∧
    Integrable (fun point : ℝ × Plane => deriv renormalization (mollification (omega point.1) index point.2) *
      fderiv ℝ (mollification (omega point.1) index) point.2 (biotSavart (omega point.1) point.2) *
        test point) (spacetimeMeasure horizon) := by
  obtain ⟨radius, radiusPositive, supported⟩ := scalarTest_spatial_support testCompact
  obtain ⟨testBound, testNonnegative, testBounded⟩ := scalarTest_uniform_bounds testSmooth testCompact
  obtain ⟨regularizedBound, regularizedNonnegative, regularizedBounded⟩ := hypotheses.uniform_mollification_bound index
  obtain ⟨valueBound, valuePositive, valueBounded⟩ :=
    ((isCompact_closedBall (0 : ℝ) regularizedBound).image smooth.continuous).isBounded.exists_pos_norm_le
  obtain ⟨derivativeBound, derivativePositive, derivativeBounded⟩ :=
    ((isCompact_closedBall (0 : ℝ) regularizedBound).image (smooth.continuous_deriv le_rfl)).isBounded.exists_pos_norm_le
  obtain ⟨velocityBound, velocityFinite, velocityBounded⟩ := hypotheses.uniform_biotSavart_bound_on_closedBall radiusPositive.le
  have velocityEstimate (time : ℝ) (inside : time ∈ Ioo 0 horizon) (position : Plane)
      (positionInside : position ∈ Metric.closedBall (0 : Plane) radius) :
      ‖biotSavart (omega time) position‖ ≤ velocityBound.toReal := by
    have estimate := ENNReal.toReal_mono velocityFinite.ne (velocityBounded time
      ⟨inside.1.le, inside.2.le⟩ position positionInside)
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using estimate
  have valueEstimate (time : ℝ) (inside : time ∈ Ioo 0 horizon) (position : Plane) :
      ‖renormalization (mollification (omega time) index position)‖ ≤ valueBound :=
    valueBounded _ ⟨mollification (omega time) index position,
      by simpa using (regularizedBounded time ⟨inside.1.le, inside.2.le⟩ position).1, rfl⟩
  have derivativeEstimate (time : ℝ) (inside : time ∈ Ioo 0 horizon) (position : Plane) :
      ‖deriv renormalization (mollification (omega time) index position)‖ ≤ derivativeBound :=
    derivativeBounded _ ⟨mollification (omega time) index position,
      by simpa using (regularizedBounded time ⟨inside.1.le, inside.2.le⟩ position).1, rfl⟩
  have regularizedMeasurable := aestronglyMeasurable_spacetime_of_measurable_Icc
    (field := fun point : ℝ × Plane => mollification (omega point.1) index point.2) nonnegative
    (hypotheses.measurable_mollification index)
  have velocityMeasurable := aestronglyMeasurable_spacetime_of_measurable_Icc
    (field := fun point : ℝ × Plane => biotSavart (omega point.1) point.2) nonnegative hypotheses.measurable_biotSavart
  have advectiveMeasurable := aestronglyMeasurable_spacetime_of_measurable_Icc
    (field := fun point : ℝ × Plane => fderiv ℝ (mollification (omega point.1) index) point.2
      (biotSavart (omega point.1) point.2)) nonnegative
    (hypotheses.measurable_mollification_advectiveDerivative index)
  have valueMeasurable := smooth.continuous.comp_aestronglyMeasurable regularizedMeasurable
  have derivativeMeasurable := (smooth.continuous_deriv le_rfl).comp_aestronglyMeasurable regularizedMeasurable
  have temporalMeasurable : AEStronglyMeasurable (timeDerivative test) (spacetimeMeasure horizon) :=
    ((testSmooth.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
  have spatialMeasurable : AEStronglyMeasurable
      (fun point : ℝ × Plane => spatialDerivative test point (biotSavart (omega point.1) point.2)) (spacetimeMeasure horizon) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((testSmooth.continuous_fderiv (by simp)).aestronglyMeasurable.prodMk
        (aestronglyMeasurable_const.prodMk velocityMeasurable))
  constructor
  · apply integrable_spacetime_of_supported_bounded (valueMeasurable.mul temporalMeasurable)
      (radius := radius) (bound := valueBound * testBound)
    · intro time inside position positionInside
      simp only [Pi.mul_apply]
      rw [norm_mul]
      exact mul_le_mul (valueEstimate time inside position) (testBounded time position).2.1 (norm_nonneg _) valuePositive.le
    · intro time inside position outside
      simp only [Pi.mul_apply, (supported time position outside).2.1, mul_zero]
  constructor
  · apply integrable_spacetime_of_supported_bounded (valueMeasurable.mul spatialMeasurable)
      (radius := radius) (bound := valueBound * (testBound * velocityBound.toReal))
    · intro time inside position positionInside
      simp only [Pi.mul_apply]
      rw [norm_mul]
      exact mul_le_mul (valueEstimate time inside position)
        (((testBounded time position).2.2 _).trans (mul_le_mul_of_nonneg_left
          (velocityEstimate time inside position positionInside) testNonnegative)) (norm_nonneg _) valuePositive.le
    · intro time inside position outside
      simp only [Pi.mul_apply, (supported time position outside).2.2, mul_zero]
  · apply integrable_spacetime_of_supported_bounded
      ((derivativeMeasurable.mul advectiveMeasurable).mul testSmooth.continuous.aestronglyMeasurable)
      (radius := radius) (bound := derivativeBound * (regularizedBound * velocityBound.toReal) * testBound)
    · intro time inside position positionInside
      simp only [Pi.mul_apply]
      rw [norm_mul, norm_mul]
      apply mul_le_mul _ (testBounded time position).1 (norm_nonneg _) (by positivity)
      apply mul_le_mul (derivativeEstimate time inside position) _ (norm_nonneg _) derivativePositive.le
      exact ((regularizedBounded time ⟨inside.1.le, inside.2.le⟩ position).2 _).trans
        (mul_le_mul_of_nonneg_left (velocityEstimate time inside position positionInside) regularizedNonnegative)
    · intro time inside position outside
      simp only [Pi.mul_apply, (supported time position outside).1, mul_zero]

end EulerNonuniqueness
