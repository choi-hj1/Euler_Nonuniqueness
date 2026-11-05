import EulerNonuniqueness.Section8.MollifiedVelocity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff InnerProductSpace

namespace EulerNonuniqueness

theorem tendsto_integral_biotSavart_mollification_quadratic {vorticity : Vorticity} {radius : ℝ}
    (nonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {coefficient : Plane → Plane →L[ℝ] Plane} (continuous : Continuous coefficient)
    (compact : HasCompactSupport coefficient) :
    Tendsto (fun index => ∫ position, ⟪biotSavart (mollification vorticity index) position,
      coefficient position (biotSavart (mollification vorticity index) position)⟫_ℝ) atTop
      (𝓝 (∫ position, ⟪biotSavart vorticity position, coefficient position (biotSavart vorticity position)⟫_ℝ)) := by
  have integrable : Integrable vorticity := memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  obtain ⟨observationRadius, observationPositive, observationBound⟩ := compact.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨bound, boundNonnegative, bounded⟩ := locally_uniform_bound_biotSavart_mollification
    nonnegative membership supported observationPositive.le
  have boundCompact : HasCompactSupport (fun position => ‖coefficient position‖ * bound ^ 2) :=
    (compact.comp_left norm_zero).mul_right
  have boundContinuous : Continuous (fun position => ‖coefficient position‖ * bound ^ 2) :=
    continuous.norm.mul continuous_const
  apply tendsto_integral_of_dominated_convergence (fun position => ‖coefficient position‖ * bound ^ 2)
  · intro index
    have velocityContinuous := continuous_biotSavart_of_continuous_compactSupport
      (contDiff_mollification integrable index).continuous (hasCompactSupport_mollification supported index)
    exact (velocityContinuous.inner (continuous.clm_apply velocityContinuous)).aestronglyMeasurable
  · exact boundContinuous.integrable_of_hasCompactSupport boundCompact
  · intro index
    exact Filter.Eventually.of_forall fun position => by
      by_cases zero : coefficient position = 0
      · simp only [zero, ContinuousLinearMap.zero_apply, inner_zero_right, norm_zero, zero_mul, le_refl]
      · have velocityBound := bounded index position (observationBound position (subset_tsupport _ zero))
        calc
          _ ≤ ‖biotSavart (mollification vorticity index) position‖ *
              ‖coefficient position (biotSavart (mollification vorticity index) position)‖ := norm_inner_le_norm _ _
          _ ≤ ‖biotSavart (mollification vorticity index) position‖ *
              (‖coefficient position‖ * ‖biotSavart (mollification vorticity index) position‖) :=
            mul_le_mul_of_nonneg_left ((coefficient position).le_opNorm _) (norm_nonneg _)
          _ = ‖coefficient position‖ * ‖biotSavart (mollification vorticity index) position‖ ^ 2 := by ring
          _ ≤ ‖coefficient position‖ * bound ^ 2 := by gcongr
  · exact Filter.Eventually.of_forall fun position =>
      (tendsto_biotSavart_mollification nonnegative membership supported position).inner
        (((coefficient position).continuous.tendsto _).comp
          (tendsto_biotSavart_mollification nonnegative membership supported position))

end EulerNonuniqueness
