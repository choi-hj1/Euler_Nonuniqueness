import EulerNonuniqueness.Section6.PaperSourceReceiverForcing
import EulerNonuniqueness.Section6.MovingPatchStrainMeasurability
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity
import EulerNonuniqueness.Section6.InitialMomentWeightedForcing

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem measurable_pointShapeForcing_first {positive negative positiveForcing negativeForcing : ℝ → ℂ}
    (positiveMeasurable : Measurable positive) (negativeMeasurable : Measurable negative)
    (firstMeasurable : Measurable positiveForcing) (secondMeasurable : Measurable negativeForcing) :
    Measurable (fun elapsed => (pointShapeForcing (positive elapsed) (negative elapsed)
      (positiveForcing elapsed) (negativeForcing elapsed)).1) := by
  have difference := (secondMeasurable.div negativeMeasurable).sub (firstMeasurable.div positiveMeasurable)
  have ratio := (negativeMeasurable.norm.pow_const (2 : ℕ)).div (positiveMeasurable.norm.pow_const (2 : ℕ))
  exact ((((measurable_const.mul ratio).mul difference.re).div_const _).add
    ((measurable_const.mul difference.im).div_const _)).div_const _

theorem measurable_complex_star {function : ℝ → ℂ} (measurable : Measurable function) :
    Measurable (fun elapsed => star (function elapsed)) :=
  Complex.conjCLE.continuous.measurable.comp measurable

structure SourcePacketPhysicalGeometry {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (scales : Scales) (source : Fin count) (start horizon chartRadius : ℝ) where
  finalTime : ℝ
  evolution : FinitePatchEvolution scales family.patchMotion finalTime
  amplitudePositive : 0 < scales.amplitude
  frequencyPositive : 0 < scales.frequency
  ratioPositive : 0 < scales.ratio
  densities : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
    patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4
  timeRange : ∀ elapsed ∈ Icc 0 horizon, start + elapsed ∈ Icc 0 finalTime
  location : ℝ → ℂ
  locationContinuous : Continuous location
  firstCenter : ℝ → ℂ
  secondCenter : ℝ → ℂ
  firstSeparation : ℝ → ℂ
  secondSeparation : ℝ → ℂ
  firstCenterContinuous : Continuous firstCenter
  secondCenterContinuous : Continuous secondCenter
  positions : ∀ elapsed ∈ Icc 0 horizon,
    relabelNegativePoints (fun patch => patchCentroid family.patchMotion (start + elapsed) source patch) =
      twoDipoleConfiguration (firstCenter elapsed) (secondCenter elapsed) (firstSeparation elapsed) (secondSeparation elapsed)
  deformation : ℝ
  deformationNonnegative : 0 ≤ deformation
  deformationSmall : deformation ≤ 1 / 16
  control : ∀ elapsed ∈ Icc 0 horizon, ∀ patch,
    BoundaryCloseToCircle scales family.patchMotion (start + elapsed) source patch deformation
  gap : ℝ
  gapPositive : 0 < gap
  radiusSmall : 4 * scales.radius (source.val + 1) ≤ gap
  separated : ∀ elapsed ∈ Icc 0 horizon, ∀ patch,
    gap ≤ ‖location elapsed - patchCentroid family.patchMotion (start + elapsed) source patch‖
  halfWidth : ℝ
  widthPositive : 0 < halfWidth
  firstBound : ∀ elapsed ∈ Icc 0 horizon, ‖firstSeparation elapsed‖ ≤ 2 * halfWidth
  secondBound : ∀ elapsed ∈ Icc 0 horizon, ‖secondSeparation elapsed‖ ≤ 2 * halfWidth
  pairSeparated : ∀ elapsed ∈ Icc 0 horizon, 4 * halfWidth ≤ ‖firstCenter elapsed - secondCenter elapsed‖
  far : ∀ elapsed ∈ Icc 0 horizon, ‖firstCenter elapsed - secondCenter elapsed‖ ≤
    ‖location elapsed - (firstCenter elapsed + secondCenter elapsed) / 2‖ / 2
  observationDistance : ℝ
  observationPositive : 0 < observationDistance
  observationLower : ∀ elapsed ∈ Icc 0 horizon,
    observationDistance ≤ ‖location elapsed - (firstCenter elapsed + secondCenter elapsed) / 2‖
  pairRadius : ℝ
  pairUpper : ∀ elapsed ∈ Icc 0 horizon, ‖firstCenter elapsed - secondCenter elapsed‖ ≤ pairRadius
  frozenDisplacement : ℂ
  frozenNonzero : frozenDisplacement ≠ 0
  displacementClose : ∀ elapsed ∈ Icc 0 horizon,
    ‖(location elapsed - (firstCenter elapsed + secondCenter elapsed) / 2) - frozenDisplacement‖ ≤ ‖frozenDisplacement‖ / 2
  positive : ℝ → ℂ
  negative : ℝ → ℂ
  idealPositive : ℝ → ℂ
  positiveContinuous : Continuous positive
  negativeContinuous : Continuous negative
  idealPositiveContinuous : Continuous idealPositive
  positiveNonzero : ∀ elapsed ∈ Icc 0 horizon, positive elapsed ≠ 0
  negativeNonzero : ∀ elapsed ∈ Icc 0 horizon, negative elapsed ≠ 0
  idealNonzero : ∀ elapsed ∈ Icc 0 horizon, idealPositive elapsed ≠ 0
  chartSmall : ∀ elapsed ∈ Icc 0 horizon,
    |(pointShapeChart (positive elapsed) (negative elapsed)).1| +
      |(pointShapeChart (positive elapsed) (negative elapsed)).2| < chartRadius
  targetMoment : ℝ → ℂ
  targetContinuous : Continuous targetMoment

namespace SourcePacketPhysicalGeometry

variable {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
  {start horizon chartRadius : ℝ}

def actualStrain (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius) (elapsed : ℝ) : ℂ :=
  vorticityComplexStrain (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (geometry.location elapsed)

def modelStrain (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius) (elapsed : ℝ) : ℂ :=
  -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * geometry.targetMoment elapsed / geometry.frozenDisplacement ^ 4)

def actualInput (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius) (elapsed : ℝ) : ℝ :=
  (pointShapeForcing (geometry.positive elapsed) (geometry.negative elapsed)
    (geometry.actualStrain elapsed * star (geometry.positive elapsed))
    (geometry.actualStrain elapsed * star (geometry.negative elapsed))).1

def modelInput (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius) (elapsed : ℝ) : ℝ :=
  rhombusConstantMomentInput geometry.idealPositive (geometry.targetMoment elapsed) geometry.frozenDisplacement elapsed

def physicalCost (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    (constant elapsed : ℝ) : ℝ :=
  constant * ‖geometry.actualStrain elapsed‖ *
      (|(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).1| +
        |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).2|) +
    4 * (4096 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 * geometry.deformation /
        (Real.pi * geometry.gap ^ 4) +
      (4 * scales.circulation (source.val + 1) * ‖centroidAsymmetry family.patchMotion (start + elapsed) source‖ /
          (Real.pi * geometry.observationDistance ^ 3) +
        3 * (‖(∫ position, quadrupoleDensity scales family.patchMotion (start + elapsed) source position •
            (position - quadrupoleCenter family.patchMotion (start + elapsed) source) ^ 2) - geometry.targetMoment elapsed‖ +
          512 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 * geometry.deformation) /
          (2 * Real.pi * geometry.observationDistance ^ 4) +
        352 * scales.circulation (source.val + 1) * geometry.pairRadius ^ 2 * geometry.halfWidth /
          (Real.pi * geometry.observationDistance ^ 5))) +
    768 * ‖geometry.targetMoment elapsed‖ *
      ‖(geometry.location elapsed - (geometry.firstCenter elapsed + geometry.secondCenter elapsed) / 2) -
        geometry.frozenDisplacement‖ / (Real.pi * ‖geometry.frozenDisplacement‖ ^ 5) +
    4 * ‖geometry.modelStrain elapsed‖ *
      ‖star (geometry.positive elapsed) / geometry.positive elapsed -
        star (geometry.idealPositive elapsed) / geometry.idealPositive elapsed‖

theorem actualInput_measurable (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius) :
    Measurable geometry.actualInput := by
  have physical := family.measurable_quadrupole_strain_along scales geometry.densities source
    (geometry.locationContinuous.measurable.comp (measurable_id.sub_const start))
  have shifted := physical.comp (measurable_const.add measurable_id : Measurable (fun elapsed : ℝ => start + elapsed))
  have strainMeasurable : Measurable geometry.actualStrain := by
    change Measurable (fun elapsed => vorticityComplexStrain
      (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (geometry.location elapsed))
    simpa only [Function.comp_def, id_eq, add_sub_cancel_left] using shifted
  exact measurable_pointShapeForcing_first geometry.positiveContinuous.measurable geometry.negativeContinuous.measurable
    (strainMeasurable.mul (measurable_complex_star geometry.positiveContinuous.measurable))
    (strainMeasurable.mul (measurable_complex_star geometry.negativeContinuous.measurable))

theorem modelInput_measurable (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius) :
    Measurable geometry.modelInput := by
  have strainMeasurable : Measurable geometry.modelStrain := by
    unfold modelStrain
    exact measurable_const.mul (measurable_complex_star
      ((measurable_const.mul geometry.targetContinuous.measurable).div_const _))
  have negativeMeasurable : Measurable (fun elapsed => Complex.I * (Real.sqrt Section2.rhombusRatio : ℂ) * geometry.idealPositive elapsed) :=
    measurable_const.mul geometry.idealPositiveContinuous.measurable
  exact measurable_pointShapeForcing_first geometry.idealPositiveContinuous.measurable negativeMeasurable
    (strainMeasurable.mul (measurable_complex_star geometry.idealPositiveContinuous.measurable))
    (strainMeasurable.mul (measurable_complex_star negativeMeasurable))

end SourcePacketPhysicalGeometry

set_option maxHeartbeats 3000000

theorem exists_source_packet_physical_comparison :
    ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
    ∀ {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count} {start horizon : ℝ},
    ∀ geometry : SourcePacketPhysicalGeometry family scales source start horizon radius,
    ∀ elapsed ∈ Icc 0 horizon,
      |geometry.actualInput elapsed - geometry.modelInput elapsed| ≤ geometry.physicalCost constant elapsed := by
  obtain ⟨constant, nonnegative, radius, positive, bound⟩ := exists_uniform_paper_source_receiver_forcing
  refine ⟨constant, nonnegative, radius, positive, ?_⟩
  intro count family scales source start horizon geometry elapsed inside
  exact bound geometry.evolution (geometry.timeRange elapsed inside) geometry.amplitudePositive geometry.frequencyPositive
    geometry.ratioPositive source (geometry.location elapsed) (geometry.firstCenter elapsed) (geometry.secondCenter elapsed)
    (geometry.firstSeparation elapsed) (geometry.secondSeparation elapsed) (geometry.targetMoment elapsed)
    geometry.frozenDisplacement (geometry.positive elapsed) (geometry.negative elapsed) (geometry.idealPositive elapsed)
    (geometry.positions elapsed inside) (geometry.control elapsed inside) geometry.deformationNonnegative geometry.deformationSmall
    geometry.gapPositive geometry.radiusSmall (geometry.separated elapsed inside) geometry.widthPositive
    (geometry.firstBound elapsed inside) (geometry.secondBound elapsed inside) (geometry.pairSeparated elapsed inside)
    (geometry.far elapsed inside) geometry.observationPositive (geometry.observationLower elapsed inside)
    (geometry.pairUpper elapsed inside) geometry.frozenNonzero (geometry.displacementClose elapsed inside)
    (geometry.positiveNonzero elapsed inside) (geometry.negativeNonzero elapsed inside) (geometry.idealNonzero elapsed inside)
    (geometry.chartSmall elapsed inside)

theorem exists_source_packet_weighted_physical_comparison :
    ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
    ∀ {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count} {start horizon decay : ℝ},
    ∀ geometry : SourcePacketPhysicalGeometry family scales source start horizon radius,
    0 ≤ horizon →
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * geometry.physicalCost constant elapsed) volume 0 horizon →
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) *
      |geometry.actualInput elapsed - geometry.modelInput elapsed|) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
      |geometry.actualInput elapsed - geometry.modelInput elapsed|) ≤
      ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.physicalCost constant elapsed := by
  obtain ⟨constant, nonnegative, radius, positive, bound⟩ := exists_source_packet_physical_comparison
  refine ⟨constant, nonnegative, radius, positive, ?_⟩
  intro count family scales source start horizon decay geometry horizonNonnegative integrable
  have measurable : Measurable (fun elapsed => Real.exp (-decay * elapsed) *
      |geometry.actualInput elapsed - geometry.modelInput elapsed|) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      (geometry.actualInput_measurable.sub geometry.modelInput_measurable).abs
  have pointwise (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      ‖Real.exp (-decay * elapsed) * |geometry.actualInput elapsed - geometry.modelInput elapsed|‖ ≤
        Real.exp (-decay * elapsed) * geometry.physicalCost constant elapsed := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_left (bound geometry elapsed inside) (Real.exp_pos _).le
  have errorIntegrable := integrable.mono_fun' measurable.aestronglyMeasurable.restrict (by
    rw [uIoc_of_le horizonNonnegative]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with elapsed inside
    exact pointwise elapsed ⟨inside.1.le, inside.2⟩)
  refine ⟨errorIntegrable, intervalIntegral.integral_mono_on horizonNonnegative errorIntegrable integrable ?_⟩
  intro elapsed inside
  simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))] using
    pointwise elapsed inside

theorem exists_source_packet_signed_physical_comparison :
    ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
    ∀ {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count} {start horizon decay : ℝ},
    ∀ geometry : SourcePacketPhysicalGeometry family scales source start horizon radius,
    0 ≤ horizon →
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * geometry.physicalCost constant elapsed) volume 0 horizon →
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * geometry.modelInput elapsed) volume 0 horizon →
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * geometry.actualInput elapsed) volume 0 horizon ∧
      |(∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.actualInput elapsed) -
        (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.modelInput elapsed)| ≤
          ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.physicalCost constant elapsed := by
  obtain ⟨constant, nonnegative, radius, positive, bound⟩ := exists_source_packet_weighted_physical_comparison
  refine ⟨constant, nonnegative, radius, positive, ?_⟩
  intro count family scales source start horizon decay geometry horizonNonnegative physicalIntegrable modelIntegrable
  obtain ⟨absoluteIntegrable, absoluteBound⟩ := bound geometry horizonNonnegative physicalIntegrable
  have measurable : Measurable (fun elapsed => Real.exp (-decay * elapsed) *
      (geometry.actualInput elapsed - geometry.modelInput elapsed)) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      (geometry.actualInput_measurable.sub geometry.modelInput_measurable)
  have normIntegrable : IntervalIntegrable (fun elapsed => ‖Real.exp (-decay * elapsed) *
      (geometry.actualInput elapsed - geometry.modelInput elapsed)‖) volume 0 horizon := by
    simpa only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using absoluteIntegrable
  have differenceIntegrable := (IntervalIntegrable.intervalIntegrable_norm_iff measurable.aestronglyMeasurable.restrict).mp normIntegrable
  have actualIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * geometry.actualInput elapsed) volume 0 horizon := by
    convert differenceIntegrable.add modelIntegrable using 1
    ext elapsed
    ring
  refine ⟨actualIntegrable, ?_⟩
  rw [← intervalIntegral.integral_sub actualIntegrable modelIntegrable]
  have estimate := intervalIntegral.norm_integral_le_integral_norm (f := fun elapsed =>
    Real.exp (-decay * elapsed) * geometry.actualInput elapsed -
      Real.exp (-decay * elapsed) * geometry.modelInput elapsed) (μ := volume) horizonNonnegative
  have errorBound : (∫ elapsed in (0 : ℝ)..horizon,
      ‖Real.exp (-decay * elapsed) * geometry.actualInput elapsed -
        Real.exp (-decay * elapsed) * geometry.modelInput elapsed‖) ≤
      ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.physicalCost constant elapsed := by
    simpa only [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using absoluteBound
  exact (by simpa only [Real.norm_eq_abs] using estimate.trans errorBound)

end EulerNonuniqueness.Paper
