import EulerNonuniqueness.Section8.RegularizedMeasurability

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff InnerProductSpace

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.integrable_momentum_terms
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (nonnegative : 0 ≤ horizon)
    {test : ℝ × Plane → Plane} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun point : ℝ × Plane => ⟪biotSavart (omega point.1) point.2, timeDerivative test point⟫_ℝ)
      (spacetimeMeasure horizon) ∧
    Integrable (fun point : ℝ × Plane => ⟪biotSavart (omega point.1) point.2,
      spatialDerivative test point (biotSavart (omega point.1) point.2)⟫_ℝ) (spacetimeMeasure horizon) := by
  obtain ⟨radius, radiusPositive, supported⟩ :=
    (compact.isCompact.image continuous_snd).isBounded.exists_pos_norm_le
  obtain ⟨derivativeBound, derivativeBounded⟩ := (compact.fderiv ℝ).exists_bound_of_continuous
    (smooth.continuous_fderiv (by simp))
  let bound := max derivativeBound 0
  have boundNonnegative : 0 ≤ bound := le_max_right _ _
  have derivativeBounded' (point : ℝ × Plane) : ‖fderiv ℝ test point‖ ≤ bound :=
    (derivativeBounded point).trans (le_max_left _ _)
  obtain ⟨velocityBound, velocityFinite, velocityBounded⟩ := hypotheses.uniform_biotSavart_bound_on_closedBall radiusPositive.le
  have velocityEstimate (time : ℝ) (inside : time ∈ Ioo 0 horizon) (position : Plane)
      (positionInside : position ∈ Metric.closedBall (0 : Plane) radius) :
      ‖biotSavart (omega time) position‖ ≤ velocityBound.toReal := by
    have estimate := ENNReal.toReal_mono velocityFinite.ne
      (velocityBounded time ⟨inside.1.le, inside.2.le⟩ position positionInside)
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using estimate
  have derivativeZero (time : ℝ) (position : Plane) (outside : position ∉ Metric.closedBall (0 : Plane) radius) :
      fderiv ℝ test (time, position) = 0 := by
    apply fderiv_of_not_mem_tsupport
    intro inside
    apply outside
    simpa using supported position ⟨(time, position), inside, rfl⟩
  have velocityMeasurable := aestronglyMeasurable_spacetime_of_measurable_Icc
    (field := fun point : ℝ × Plane => biotSavart (omega point.1) point.2) nonnegative hypotheses.measurable_biotSavart
  have derivativeMeasurable := (smooth.continuous_fderiv (by simp)).aestronglyMeasurable (μ := spacetimeMeasure horizon)
  have temporalMeasurable : AEStronglyMeasurable (fun point => timeDerivative test point) (spacetimeMeasure horizon) :=
    ((smooth.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
    (μ := spacetimeMeasure horizon)
  have spatialMeasurable : AEStronglyMeasurable
      (fun point => spatialDerivative test point (biotSavart (omega point.1) point.2)) (spacetimeMeasure horizon) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (derivativeMeasurable.prodMk (aestronglyMeasurable_const.prodMk velocityMeasurable))
  constructor
  · apply integrable_spacetime_of_supported_bounded (velocityMeasurable.inner temporalMeasurable)
      (radius := radius) (bound := velocityBound.toReal * bound)
    · intro time inside position positionInside
      have temporalBound : ‖timeDerivative test (time, position)‖ ≤ bound := by
        have estimate := ((fderiv ℝ test (time, position)).le_opNorm (1, 0)).trans
          (mul_le_mul_of_nonneg_right (derivativeBounded' (time, position)) (norm_nonneg (1, (0 : Plane))))
        simpa only [timeDerivative, Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one, mul_one] using estimate
      exact (norm_inner_le_norm _ _).trans (mul_le_mul (velocityEstimate time inside position positionInside)
        temporalBound (norm_nonneg _) ENNReal.toReal_nonneg)
    · intro time inside position outside
      simp only [timeDerivative, derivativeZero time position outside, ContinuousLinearMap.zero_apply, inner_zero_right]
  · apply integrable_spacetime_of_supported_bounded (velocityMeasurable.inner spatialMeasurable)
      (radius := radius) (bound := velocityBound.toReal * (bound * velocityBound.toReal))
    · intro time inside position positionInside
      have spatialBound : ‖spatialDerivative test (time, position) (biotSavart (omega time) position)‖ ≤
          bound * ‖biotSavart (omega time) position‖ := by
        have estimate := ((fderiv ℝ test (time, position)).le_opNorm (0, biotSavart (omega time) position)).trans
          (mul_le_mul_of_nonneg_right (derivativeBounded' (time, position)) (norm_nonneg (0, biotSavart (omega time) position)))
        simpa only [spatialDerivative, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using estimate
      exact (norm_inner_le_norm _ _).trans (mul_le_mul (velocityEstimate time inside position positionInside)
        (spatialBound.trans (mul_le_mul_of_nonneg_left (velocityEstimate time inside position positionInside) boundNonnegative))
        (norm_nonneg _) ENNReal.toReal_nonneg)
    · intro time inside position outside
      simp only [spatialDerivative, derivativeZero time position outside, ContinuousLinearMap.zero_apply, inner_zero_right]

end EulerNonuniqueness
