import EulerNonuniqueness.Section6.SourcePacketLiteralChartCost

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem source_packet_measurable_pointShapeChart {positive negative : ℝ → ℂ}
    (positiveMeasurable : Measurable positive) (negativeMeasurable : Measurable negative) :
    Measurable (fun elapsed => pointShapeChart (positive elapsed) (negative elapsed)) := by
  have ratio := (negativeMeasurable.norm.pow_const (2 : ℕ)).div (positiveMeasurable.norm.pow_const (2 : ℕ))
  have argument := Complex.measurable_arg.comp ((negativeMeasurable.div positiveMeasurable).pow_const (2 : ℕ))
  have angle : Measurable (fun elapsed => unwrappedShapeArgument ((negative elapsed / positive elapsed) ^ 2)) :=
    Measurable.ite (measurableSet_lt argument measurable_const) (argument.add_const _) argument
  exact (((ratio.div_const _).sub_const _).add ((angle.sub_const _).div_const _)).div_const _ |>.prodMk
    ((((ratio.div_const _).sub_const _).sub ((angle.sub_const _).div_const _)).div_const _)

namespace SourcePacketPhysicalGeometry

variable {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
  {start horizon chartRadius : ℝ}

theorem sourceCost_continuous (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius) :
    Continuous geometry.sourceCost := by
  have shift : Continuous (fun elapsed : ℝ => start + elapsed) := continuous_const.add continuous_id
  have moment := (family.quadrupole_complex_moment_continuous scales source).comp shift
  have asymmetry : Continuous (fun elapsed => centroidAsymmetry family.patchMotion (start + elapsed) source) := by
    have centroid (patch : Fin 4) := (family.patchCentroid_continuous source patch).comp shift
    exact ((((centroid 0).add (centroid 1)).sub (centroid 2)).sub (centroid 3)).div_const 4
  have target := geometry.targetContinuous
  have location := geometry.locationContinuous
  have firstCenter := geometry.firstCenterContinuous
  have secondCenter := geometry.secondCenterContinuous
  unfold sourceCost
  fun_prop

theorem weighted_chart_cost_le_literal_cost (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    {constant chartBound decay : ℝ} (horizonNonnegative : 0 ≤ horizon) (constantNonnegative : 0 ≤ constant)
    (chartSmall : ∀ elapsed ∈ Icc 0 horizon,
      |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).1| +
        |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).2| ≤ chartBound) :
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * (constant * ‖geometry.actualStrain elapsed‖ *
      (|(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).1| +
        |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).2|))) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * (constant * ‖geometry.actualStrain elapsed‖ *
      (|(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).1| +
        |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).2|))) ≤
      (constant * chartBound / 4) *
        ((6 / (Real.pi * ‖geometry.frozenDisplacement‖ ^ 4)) *
          (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖geometry.targetMoment elapsed‖) +
        ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.sourceCost elapsed) := by
  have physical := family.measurable_quadrupole_strain_along scales geometry.densities source
    (geometry.locationContinuous.measurable.comp (measurable_id.sub_const start))
  have actualMeasurable : Measurable geometry.actualStrain := by
    simpa only [actualStrain, Function.comp_def, id_eq, add_sub_cancel_left] using
      physical.comp (measurable_const.add measurable_id : Measurable (fun elapsed : ℝ => start + elapsed))
  have chartMeasurable := source_packet_measurable_pointShapeChart geometry.positiveContinuous.measurable geometry.negativeContinuous.measurable
  have measurable : Measurable (fun elapsed => Real.exp (-decay * elapsed) * (constant * ‖geometry.actualStrain elapsed‖ *
      (|(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).1| +
        |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).2|))) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      ((measurable_const.mul actualMeasurable.norm).mul (chartMeasurable.fst.abs.add chartMeasurable.snd.abs))
  let majorant := fun elapsed => (constant * chartBound / 4) *
    (Real.exp (-decay * elapsed) * ((6 / (Real.pi * ‖geometry.frozenDisplacement‖ ^ 4)) *
      ‖geometry.targetMoment elapsed‖ + geometry.sourceCost elapsed))
  have target := geometry.targetContinuous
  have cost := geometry.sourceCost_continuous
  have majorantContinuous : Continuous majorant := by
    dsimp only [majorant]
    fun_prop
  have pointwise (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      ‖Real.exp (-decay * elapsed) * (constant * ‖geometry.actualStrain elapsed‖ *
        (|(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).1| +
          |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).2|))‖ ≤ majorant elapsed := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have bound := mul_le_mul_of_nonneg_left (geometry.chart_cost_le_literal_cost inside constantNonnegative
      (chartSmall elapsed inside)) (Real.exp_pos (-decay * elapsed)).le
    convert bound using 1 <;> dsimp only [majorant] <;> ring
  have integrable := (majorantContinuous.intervalIntegrable (μ := volume) 0 horizon).mono_fun' measurable.aestronglyMeasurable.restrict (by
    rw [uIoc_of_le horizonNonnegative]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with elapsed inside
    exact pointwise elapsed ⟨inside.1.le, inside.2⟩)
  refine ⟨integrable, (intervalIntegral.integral_mono_on horizonNonnegative integrable
    (majorantContinuous.intervalIntegrable 0 horizon) (fun elapsed inside => (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using pointwise elapsed inside))).trans_eq ?_⟩
  dsimp only [majorant]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have targetContinuous : Continuous (fun elapsed : ℝ => Real.exp (-decay * elapsed) * ‖geometry.targetMoment elapsed‖) := by fun_prop
  have costContinuous : Continuous (fun elapsed : ℝ => Real.exp (-decay * elapsed) * geometry.sourceCost elapsed) := by fun_prop
  simp_rw [mul_add, mul_left_comm (Real.exp _) (6 / (Real.pi * ‖geometry.frozenDisplacement‖ ^ 4))]
  rw [intervalIntegral.integral_add ((continuous_const.mul targetContinuous).intervalIntegrable 0 horizon)
    (costContinuous.intervalIntegrable 0 horizon), intervalIntegral.integral_const_mul]

end SourcePacketPhysicalGeometry

end EulerNonuniqueness.Paper
