import EulerNonuniqueness.Section6.SourcePacketVectorProjectionBound
import EulerNonuniqueness.Section6.SourcePacketPhysicalCostAssembly
import EulerNonuniqueness.Section6.SourcePacketRetainedTargetMoment

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

namespace SourcePacketPhysicalGeometry

variable {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
  {start horizon chartRadius : ℝ}

def pairedShapeInput (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    (referenceStrain : ℝ → ℂ) (elapsed : ℝ) : ℝ × ℝ :=
  pointShapeForcing (geometry.positive elapsed) (geometry.negative elapsed)
    ((geometry.actualStrain elapsed - referenceStrain elapsed) * star (geometry.positive elapsed))
    ((geometry.actualStrain elapsed - referenceStrain elapsed) * star (geometry.negative elapsed))

theorem pairedShapeInput_measurable (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    {referenceStrain : ℝ → ℂ} (referenceMeasurable : Measurable referenceStrain) :
    Measurable (geometry.pairedShapeInput referenceStrain) := by
  have physical := family.measurable_quadrupole_strain_along scales geometry.densities source
    (geometry.locationContinuous.measurable.comp (measurable_id.sub_const start))
  have shifted := physical.comp (measurable_const.add measurable_id : Measurable (fun elapsed : ℝ => start + elapsed))
  have strainMeasurable : Measurable geometry.actualStrain := by
    change Measurable (fun elapsed => vorticityComplexStrain
      (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (geometry.location elapsed))
    simpa only [Function.comp_def, id_eq, add_sub_cancel_left] using shifted
  exact measurable_pointShapeForcing_vector geometry.positiveContinuous.measurable geometry.negativeContinuous.measurable
    ((strainMeasurable.sub referenceMeasurable).mul (measurable_complex_star geometry.positiveContinuous.measurable))
    ((strainMeasurable.sub referenceMeasurable).mul (measurable_complex_star geometry.negativeContinuous.measurable))

theorem sourceCost_le_physicalCost_zero
    (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius) (elapsed : ℝ) :
    geometry.sourceCost elapsed ≤ geometry.physicalCost 0 elapsed := by
  rw [geometry.physicalCost_eq_chart_source_phase]
  simp only [zero_mul, zero_add]
  exact le_add_of_nonneg_right (by unfold phaseCost; positivity)

end SourcePacketPhysicalGeometry

set_option maxHeartbeats 6000000

theorem exists_source_packet_paired_vector_norm_upper :
    ∃ radius > (0 : ℝ),
    ∀ {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count} {start horizon : ℝ},
    ∀ geometry : SourcePacketPhysicalGeometry family scales source start horizon radius,
    ∀ referenceStrain : ℝ → ℂ, Measurable referenceStrain →
    ∀ outgoingPhase momentBudget costBudget referenceBudget : ℝ, 0 ≤ horizon →
    let decay := 2 * Real.sqrt 2 * scales.omega source.val
    let distance := ‖geometry.frozenDisplacement‖
    let seed := Real.sqrt 3 * scales.circulation (source.val + 1) ^ 2 /
      (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega source.val ^ 2 * distance ^ 4)
    let initialMoment := ∫ position, quadrupoleDensity scales family.patchMotion start source position •
      (position - quadrupoleCenter family.patchMotion start source) ^ 2
    (∀ elapsed, geometry.targetMoment elapsed = initialMoment + separatingLeadingMoment
      (scales.circulation (source.val + 1)) outgoingPhase elapsed) →
    6 * ‖initialMoment‖ / (Real.pi * distance ^ 4 * decay) ≤ momentBudget * seed →
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * geometry.physicalCost 0 elapsed) volume 0 horizon →
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.physicalCost 0 elapsed) ≤ costBudget * seed →
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * ‖referenceStrain elapsed‖) volume 0 horizon →
    4 * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖referenceStrain elapsed‖) ≤ referenceBudget * seed →
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * ‖geometry.pairedShapeInput referenceStrain elapsed‖) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖geometry.pairedShapeInput referenceStrain elapsed‖) ≤
      (5 / 4 : ℝ) * (momentBudget + 3 + costBudget + referenceBudget) * seed := by
  obtain ⟨radius, radiusPositive, projection⟩ := exists_reference_strain_vector_projection_bound
  refine ⟨radius, radiusPositive, ?_⟩
  intro count family scales source start horizon geometry referenceStrain referenceMeasurable outgoingPhase momentBudget costBudget referenceBudget horizonNonnegative
  dsimp only
  intro targetEquation inheritedBound physicalIntegrable physicalBound referenceIntegrable referenceBound
  let decay := 2 * Real.sqrt 2 * scales.omega source.val
  let distance := ‖geometry.frozenDisplacement‖
  let seed := Real.sqrt 3 * scales.circulation (source.val + 1) ^ 2 /
    (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega source.val ^ 2 * distance ^ 4)
  let initialMoment := ∫ position, quadrupoleDensity scales family.patchMotion start source position •
    (position - quadrupoleCenter family.patchMotion start source) ^ 2
  let coefficient := 6 / (Real.pi * distance ^ 4)
  let targetWeighted := fun elapsed => Real.exp (-decay * elapsed) * ‖geometry.targetMoment elapsed‖
  let physicalWeighted := fun elapsed => Real.exp (-decay * elapsed) * geometry.physicalCost 0 elapsed
  let referenceWeighted := fun elapsed => Real.exp (-decay * elapsed) * ‖referenceStrain elapsed‖
  let actualWeighted := fun elapsed => Real.exp (-decay * elapsed) * ‖geometry.pairedShapeInput referenceStrain elapsed‖
  let majorant := fun elapsed => (5 / 4 : ℝ) *
    ((coefficient * targetWeighted elapsed + physicalWeighted elapsed) + 4 * referenceWeighted elapsed)
  have targetIntegrable : IntervalIntegrable targetWeighted volume 0 horizon :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul geometry.targetContinuous.norm).intervalIntegrable _ _
  have majorantIntegrable : IntervalIntegrable majorant volume 0 horizon :=
    (((targetIntegrable.const_mul coefficient).add physicalIntegrable).add (referenceIntegrable.const_mul 4)).const_mul (5 / 4)
  have pointwise (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : actualWeighted elapsed ≤ majorant elapsed := by
    have projected := projection (geometry.positive elapsed) (geometry.negative elapsed)
      (geometry.actualStrain elapsed - referenceStrain elapsed)
      (geometry.positiveNonzero elapsed inside) (geometry.negativeNonzero elapsed inside) (geometry.chartSmall elapsed inside).le
    have literal := geometry.actual_strain_le_literal_cost inside
    have physical := geometry.sourceCost_le_physicalCost_zero elapsed
    have triangle := norm_sub_le (geometry.actualStrain elapsed) (referenceStrain elapsed)
    have unweighted : ‖geometry.pairedShapeInput referenceStrain elapsed‖ ≤ (5 / 4 : ℝ) *
        ((coefficient * ‖geometry.targetMoment elapsed‖ + geometry.physicalCost 0 elapsed) + 4 * ‖referenceStrain elapsed‖) := by
      change ‖geometry.pairedShapeInput referenceStrain elapsed‖ ≤ 5 * ‖geometry.actualStrain elapsed - referenceStrain elapsed‖ at projected
      change 4 * ‖geometry.actualStrain elapsed‖ ≤ coefficient * ‖geometry.targetMoment elapsed‖ + geometry.sourceCost elapsed at literal
      linarith
    have multiplied := mul_le_mul_of_nonneg_left unweighted (Real.exp_pos (-decay * elapsed)).le
    convert multiplied using 1 <;> dsimp only [actualWeighted, majorant, targetWeighted, physicalWeighted, referenceWeighted] <;> ring
  have measurable : Measurable actualWeighted :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul (geometry.pairedShapeInput_measurable referenceMeasurable).norm
  have actualIntegrable := majorantIntegrable.mono_fun' measurable.aestronglyMeasurable.restrict (by
    rw [uIoc_of_le horizonNonnegative]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with elapsed inside
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
    exact pointwise elapsed ⟨inside.1.le, inside.2⟩)
  have integrated := intervalIntegral.integral_mono_on horizonNonnegative actualIntegrable majorantIntegrable pointwise
  have majorantIntegral : (∫ elapsed in (0 : ℝ)..horizon, majorant elapsed) =
      (5 / 4 : ℝ) * ((coefficient * (∫ elapsed in (0 : ℝ)..horizon, targetWeighted elapsed) +
        (∫ elapsed in (0 : ℝ)..horizon, physicalWeighted elapsed)) +
        4 * (∫ elapsed in (0 : ℝ)..horizon, referenceWeighted elapsed)) := by
    dsimp only [majorant]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add ((targetIntegrable.const_mul coefficient).add physicalIntegrable) (referenceIntegrable.const_mul 4),
      intervalIntegral.integral_add (targetIntegrable.const_mul coefficient) physicalIntegrable]
    simp only [intervalIntegral.integral_const_mul]
    rfl
  rw [majorantIntegral] at integrated
  have targetBound := scales.retained_target_moment_weighted_bound source.val geometry.frequencyPositive geometry.ratioPositive
    initialMoment outgoingPhase horizon distance momentBudget horizonNonnegative (norm_pos_iff.mpr geometry.frozenNonzero) inheritedBound
  have targetBudget : coefficient * (∫ elapsed in (0 : ℝ)..horizon, targetWeighted elapsed) ≤ (momentBudget + 3) * seed := by
    simpa only [coefficient, targetWeighted, decay, seed, targetEquation, initialMoment, distance] using targetBound
  have combined := mul_le_mul_of_nonneg_left (add_le_add (add_le_add targetBudget physicalBound) referenceBound)
    (by norm_num : (0 : ℝ) ≤ 5 / 4)
  refine ⟨actualIntegrable, integrated.trans ?_⟩
  convert combined using 1 <;> dsimp only [physicalWeighted, referenceWeighted, decay, seed, distance] <;> ring

end EulerNonuniqueness.Paper
