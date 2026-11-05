import EulerNonuniqueness.Section5.CascadePhysicalStageData
import EulerNonuniqueness.Section5.UniversalIncomingMatchStop
import EulerNonuniqueness.Section7.ActualStoppedCascadeApproximation

noncomputable section
open Set Filter
open scoped Topology
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

/-- Physical matching records rule out every premature internal stop. -/
theorem exists_universal_source_stop_one_of_physical_stage_data
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (sectionTime incomingTime : ℝ) (timeOrder : incomingTime < sectionTime)
    {factor error : ℝ} (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8)
    (errorPositive : 0 < error) (errorSmall : error ≤ 1 / 64)
    (referenceSeparated : ∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
      2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) target -
        centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) source‖)
    (radiusLarge : 512 ≤ separationRadius orbit sectionTime)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ error / 2)
    (outgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re) :
    ∃ stopTolerance > (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {threshold scaleRoot boundaryConstant : ℝ}, 0 < scaleRoot → 0 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {count : ℕ} {phase dipoleAngle : ℕ → ℝ} {referenceConstant shapeRadius monitor rawCap : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, threshold ≤ 1 / 2 →
    ∀ extent magnitude coefficient phaseTolerance timingTolerance : ℝ,
    (∀ index : Fin count, CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance stopTolerance) → path.stop = 1 := by
  obtain ⟨stopTolerance, stopPositive, stops⟩ := exists_universal_material_stop_one_of_incoming_matches
    orbit normalized sectionTime incomingTime timeOrder factorPositive factorSmall errorPositive errorSmall
      referenceSeparated radiusLarge separationClose outgoing
  refine ⟨stopTolerance, stopPositive, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold scaleRoot boundaryConstant rootPositive boundaryNonnegative
  filter_upwards [stops scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative] with frequency stop
  intro count phase dipoleAngle referenceConstant shapeRadius monitor rawCap prepared path thresholdSmall
    extent magnitude coefficient phaseTolerance timingTolerance records
  apply stop count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path thresholdSmall
  intro index nonterminal
  obtain ⟨hit, hitInside, rotation, rotationNorm, matching⟩ := (records index).previousMatch nonterminal
  exact Or.inr ⟨hit, ⟨hitInside.1, hitInside.2.trans (records index).entryInside.2⟩,
    rotation, rotationNorm, matching⟩

/-- Actual families of physical records yield approximation data; neither stop one nor outgoing geometry is assumed. -/
theorem exists_universal_approximationData_of_physical_stage_families
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (sectionTime incomingTime : ℝ) (timeOrder : incomingTime < sectionTime)
    {factor error : ℝ} (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8)
    (errorPositive : 0 < error) (errorSmall : error ≤ 1 / 64)
    (referenceSeparated : ∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
      2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) target -
        centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) source‖)
    (radiusLarge : 2048 ≤ separationRadius orbit sectionTime)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ error / 2)
    (outgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re) :
    ∃ stopTolerance > (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {threshold scaleRoot boundaryConstant referenceConstant : ℝ}, threshold ≤ 1 / 8 →
    0 < scaleRoot → 0 ≤ boundaryConstant → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop,
    ∀ truncations : ℕ → ℕ, Tendsto truncations atTop atTop →
    ∀ phase dipoleAngle : ℕ → ℕ → ℝ, ∀ shapeRadius monitor rawCap : ℕ → ℝ,
    ∀ prepared : (family : ℕ) → CascadeSourcePreparedPair (rawCap family) {scales with frequency := frequency} orbit sectionTime
      (phase family) (dipoleAngle family) threshold referenceConstant scaleRoot (shapeRadius family) factor (monitor family)
      boundaryConstant (truncations family + 1),
    ∀ paths : (family : ℕ) → CascadeInternallyStoppedPath (prepared family).toCascadeMaterialPreparedPair,
    ∀ extent magnitude coefficient phaseTolerance timingTolerance : ℝ,
    ∀ records : (family : ℕ) → (index : Fin (truncations family + 1)) →
      CascadePhysicalStageData (prepared family) (paths family) index incomingTime extent magnitude coefficient error
        phaseTolerance timingTolerance stopTolerance,
    (∀ family : ℕ, (records family ⟨0, by omega⟩).entry ≤ 1 / 2) → Nonempty ApproximationData := by
  obtain ⟨stopTolerance, stopPositive, stops⟩ := exists_universal_source_stop_one_of_physical_stage_data
    orbit normalized sectionTime incomingTime timeOrder factorPositive factorSmall errorPositive errorSmall referenceSeparated
      ((by norm_num : (512 : ℝ) ≤ 2048).trans radiusLarge) separationClose outgoing
  refine ⟨stopTolerance, stopPositive, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold scaleRoot boundaryConstant referenceConstant
    thresholdSmall rootPositive boundaryNonnegative referenceNonnegative
  filter_upwards [stops scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative,
    scales.eventually_approximationData_of_actual_stopped_outgoing_cascades amplitudePositive ratioBound alphaPositive
      orbit sectionTime factorPositive (factorSmall.trans (by norm_num)) thresholdSmall rootPositive boundaryNonnegative referenceNonnegative,
    eventually_ge_atTop (max 1 (16 * separationRadius orbit sectionTime))] with frequency stop approximation frequencyLarge
  intro truncations truncationsTendsto phase dipoleAngle shapeRadius monitor rawCap prepared paths
    extent magnitude coefficient phaseTolerance timingTolerance records outerSmall
  let changed : Scales := {scales with frequency := frequency}
  let outer : (family : ℕ) → Fin (truncations family + 1) := fun _ => ⟨0, by omega⟩
  let start := fun family => (records family (outer family)).entry
  let direction := fun family => (records family (outer family)).direction
  have stopOne (family : ℕ) : (paths family).stop = 1 :=
    stop (prepared family) (paths family) (thresholdSmall.trans (by norm_num))
      extent magnitude coefficient phaseTolerance timingTolerance (records family)
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le ((le_max_left _ _).trans frequencyLarge)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have distanceSmall : separationRadius orbit sectionTime ≤ changed.omega 1 / 16 := by
    have omegaBound := changed.omega_ge_frequency frequencyPositive
      (by change 1 ≤ scales.ratio; linarith only [ratioBound]) 1
    have frequencyBound : 16 * separationRadius orbit sectionTime ≤ frequency := (le_max_right _ _).trans frequencyLarge
    linarith only [omegaBound, frequencyBound]
  apply approximation truncations truncationsTendsto phase dipoleAngle shapeRadius monitor
    (fun family => (prepared family).toCascadeMaterialPreparedPair) paths stopOne start
      (fun _ => separationRadius orbit sectionTime) direction
    (fun family => (records family (outer family)).entryInside.1) outerSmall
    (fun _ => (by norm_num : (512 : ℝ) ≤ 2048).trans radiusLarge) (fun _ => distanceSmall)
    (fun family => (records family (outer family)).directionNorm)
  intro family
  let data := records family (outer family)
  have lengthPositive := changed.length_pos 1
  have weak := mul_le_mul_of_nonneg_right errorSmall lengthPositive.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [data, outer, start, direction, Nat.zero_add] using
      data.firstError.trans (by simpa only [outer, one_div, mul_comm, div_eq_mul_inv, one_mul] using weak)
  · simpa only [data, outer, start, direction, Nat.zero_add] using
      data.secondError.trans (by simpa only [outer, one_div, mul_comm, div_eq_mul_inv, one_mul] using weak)
  · simpa only [data, outer, start, direction, Nat.zero_add] using data.outgoingProjection
  · simpa only [data, outer, start, direction, Nat.zero_add] using data.centerUpper

end EulerNonuniqueness.Paper
