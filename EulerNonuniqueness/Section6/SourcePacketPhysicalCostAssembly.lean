import EulerNonuniqueness.Section6.SourcePacketWeightedChartCost

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.SourcePacketPhysicalGeometry

open EulerNonuniqueness.Section6

variable {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
  {start horizon chartRadius : ℝ}

def phaseCost (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius) (elapsed : ℝ) : ℝ :=
  4 * ‖geometry.modelStrain elapsed‖ *
    ‖star (geometry.positive elapsed) / geometry.positive elapsed -
      star (geometry.idealPositive elapsed) / geometry.idealPositive elapsed‖

theorem physicalCost_eq_chart_source_phase
    (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius) (constant elapsed : ℝ) :
    geometry.physicalCost constant elapsed = constant * ‖geometry.actualStrain elapsed‖ *
        (|(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).1| +
          |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).2|) +
      geometry.sourceCost elapsed + geometry.phaseCost elapsed := by
  unfold physicalCost sourceCost phaseCost
  ring

theorem phaseCost_intervalIntegrable (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    {decay : ℝ} (horizonNonnegative : 0 ≤ horizon) :
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * geometry.phaseCost elapsed) volume 0 horizon := by
  have target := geometry.targetContinuous
  have model : Continuous geometry.modelStrain := by unfold modelStrain; fun_prop
  have positive := geometry.positiveContinuous.measurable
  have ideal := geometry.idealPositiveContinuous.measurable
  have measurable : Measurable (fun elapsed => Real.exp (-decay * elapsed) * geometry.phaseCost elapsed) := by
    exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      ((measurable_const.mul model.measurable.norm).mul
        (((measurable_complex_star positive).div positive).sub ((measurable_complex_star ideal).div ideal)).norm)
  have majorant : Continuous (fun elapsed : ℝ => Real.exp (-decay * elapsed) * (8 * ‖geometry.modelStrain elapsed‖)) := by fun_prop
  apply (majorant.intervalIntegrable (μ := volume) 0 horizon).mono_fun' measurable.aestronglyMeasurable.restrict
  rw [uIoc_of_le horizonNonnegative]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with elapsed inside
  have inside : elapsed ∈ Icc 0 horizon := ⟨inside.1.le, inside.2⟩
  have positiveNorm : ‖star (geometry.positive elapsed) / geometry.positive elapsed‖ = 1 := by
    rw [norm_div, norm_star, div_self (norm_ne_zero_iff.mpr (geometry.positiveNonzero elapsed inside))]
  have idealNorm : ‖star (geometry.idealPositive elapsed) / geometry.idealPositive elapsed‖ = 1 := by
    rw [norm_div, norm_star, div_self (norm_ne_zero_iff.mpr (geometry.idealNonzero elapsed inside))]
  have orientation := norm_sub_le (star (geometry.positive elapsed) / geometry.positive elapsed)
    (star (geometry.idealPositive elapsed) / geometry.idealPositive elapsed)
  rw [positiveNorm, idealNorm] at orientation
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold phaseCost; positivity)]
  unfold phaseCost
  nlinarith [mul_le_mul_of_nonneg_left orientation
    (show 0 ≤ Real.exp (-decay * elapsed) * 4 * ‖geometry.modelStrain elapsed‖ by positivity)]

theorem weighted_physicalCost_integrable
    (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    {constant decay : ℝ} (horizonNonnegative : 0 ≤ horizon) (constantNonnegative : 0 ≤ constant) :
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * geometry.physicalCost constant elapsed) volume 0 horizon := by
  have chart := (geometry.weighted_chart_cost_le_literal_cost (decay := decay) horizonNonnegative constantNonnegative
    (fun elapsed inside => (geometry.chartSmall elapsed inside).le)).1
  have cost := geometry.sourceCost_continuous
  have sourceIntegrable : IntervalIntegrable (fun elapsed : ℝ => Real.exp (-decay * elapsed) * geometry.sourceCost elapsed)
      volume 0 horizon := by apply Continuous.intervalIntegrable; fun_prop
  have phase := geometry.phaseCost_intervalIntegrable (decay := decay) horizonNonnegative
  convert (chart.add sourceIntegrable).add phase using 1
  funext elapsed
  rw [geometry.physicalCost_eq_chart_source_phase]
  ring

theorem weighted_physicalCost_le_literal_budgets
    (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    {constant chartBound decay sourceBudget targetBudget phaseBudget seed : ℝ}
    (horizonNonnegative : 0 ≤ horizon) (constantNonnegative : 0 ≤ constant)
    (chartSmall : ∀ elapsed ∈ Icc 0 horizon,
      |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).1| +
        |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).2| ≤ chartBound)
    (sourceBound : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.sourceCost elapsed) ≤ sourceBudget * seed)
    (targetBound : (6 / (Real.pi * ‖geometry.frozenDisplacement‖ ^ 4)) *
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖geometry.targetMoment elapsed‖) ≤ targetBudget * seed)
    (phaseBound : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.phaseCost elapsed) ≤ phaseBudget * seed) :
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.physicalCost constant elapsed) ≤
      ((constant * chartBound / 4) * (targetBudget + sourceBudget) + sourceBudget + phaseBudget) * seed := by
  obtain ⟨chartIntegrable, chart⟩ := geometry.weighted_chart_cost_le_literal_cost horizonNonnegative constantNonnegative chartSmall
  have chartNonnegative : 0 ≤ chartBound :=
    (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (chartSmall 0 ⟨le_rfl, horizonNonnegative⟩)
  have budget := mul_le_mul_of_nonneg_left (add_le_add targetBound sourceBound)
    (show 0 ≤ constant * chartBound / 4 by positivity)
  have chartBound := chart.trans budget
  have cost := geometry.sourceCost_continuous
  have sourceIntegrable : IntervalIntegrable (fun elapsed : ℝ => Real.exp (-decay * elapsed) * geometry.sourceCost elapsed)
      volume 0 horizon := by apply Continuous.intervalIntegrable; fun_prop
  have phaseIntegrable := geometry.phaseCost_intervalIntegrable (decay := decay) horizonNonnegative
  have equality : (fun elapsed => Real.exp (-decay * elapsed) * geometry.physicalCost constant elapsed) =
      fun elapsed => (Real.exp (-decay * elapsed) * (constant * ‖geometry.actualStrain elapsed‖ *
        (|(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).1| +
          |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).2|)) +
        Real.exp (-decay * elapsed) * geometry.sourceCost elapsed) +
        Real.exp (-decay * elapsed) * geometry.phaseCost elapsed := by
    funext elapsed
    rw [geometry.physicalCost_eq_chart_source_phase]
    ring
  rw [equality, intervalIntegral.integral_add (chartIntegrable.add sourceIntegrable) phaseIntegrable,
    intervalIntegral.integral_add chartIntegrable sourceIntegrable]
  have combined := add_le_add (add_le_add chartBound sourceBound) phaseBound
  convert combined using 1 <;> ring

end EulerNonuniqueness.Paper.SourcePacketPhysicalGeometry
