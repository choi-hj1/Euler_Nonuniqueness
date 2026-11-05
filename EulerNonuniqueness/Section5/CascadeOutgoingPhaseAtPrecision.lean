import EulerNonuniqueness.Section5.CascadeCanonicalOutgoingPhaseCoordinateBound
import EulerNonuniqueness.Section6.HalfDiagonalMatchingPhase
import EulerNonuniqueness.Section5.CascadeFullStatePhysicalRefinement
import EulerNonuniqueness.Section1.UniformIntegratedReferenceIndexBudget
import EulerNonuniqueness.Section5.Delay

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_outgoing_phase_at_precision
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit) (sectionTime : ℝ)
    (factor : ℝ) (factorPositive : 0 < factor)
    (fullMagnitude : ℝ) (fullNonnegative : 0 ≤ fullMagnitude)
    (phaseTolerance : ℝ) (phasePositive : 0 < phaseTolerance) :
    ∃ endpointMax > (0 : ℝ), endpointMax ≤ 1 ∧
    ∀ᶠ incomingTime : ℝ in atBot,
    ∀ scales : Scales, 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), ∀ {threshold scaleRoot boundaryConstant : ℝ},
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {phase dipoleAngle : ℕ → ℝ} {rawCap shapeRadius monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    PrescribedCascadePhases {scales with frequency := frequency} orbit sectionTime count phase dipoleAngle →
    ∀ index : Fin count, index.val + 1 < count → ∀ hit ∈ Icc 0 path.stop,
    ∀ origin contact endpoint : ℝ, 0 < endpoint → endpoint ≤ endpointMax →
    (∀ time ∈ Icc 0 hit,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 4) →
    ∀ lift : Fin 2 → ℝ → ℝ,
    (∀ side, ContinuousOn (lift side) (Icc 0 hit)) →
    (∀ side, lift side 0 = phase (index.val + 1)) →
    (∀ side, ∀ time ∈ Icc 0 hit,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
          Complex.exp (Complex.I * (lift side time : ℂ))) →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
    (∀ time ∈ Icc 0 hit, prepared.finiteCoordinateSize graph coordinate lift index time +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
        fullMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - origin))) →
    changed.seed (index.val + 1) * Real.exp (growth * (hit - origin)) ≤ endpoint →
    |changed.omega (index.val + 1) * (contact - hit) - (sectionTime - incomingTime)| ≤ phaseTolerance / 8 →
    ∀ rotation : ℂ,
    halfDiagonalMatchingRotation (positiveHalfDiagonal motion hit index) (orbit.positive incomingTime) = rotation →
    let outgoingPhase := lift 0 hit - orbit.phase incomingTime + orbit.limitingDipoleAngle
    Complex.exp (Complex.I * (outgoingPhase : ℂ)) =
      rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ)) ∧
    ∃ winding : ℤ,
      |outgoingPhase - dipoleAngle (index.val + 1) + changed.omega (index.val + 1) *
        (contact - changed.predictedTime sectionTime count (index.val + 1)) - (winding : ℝ) * Real.pi| ≤ phaseTolerance := by
  obtain ⟨phaseRadius, phaseRadiusPositive, constant, constantOne, phaseBounds⟩ :=
    exists_uniform_canonical_outgoing_phase_coordinate_bound graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  have constantPositive : 0 < constant := zero_lt_one.trans_le constantOne
  obtain ⟨physicalPrecision, physicalPositive, physicalFactory⟩ :=
    exists_uniform_actual_full_state_physical_refinement graphAnalytic.contDiffAt coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative phaseRadiusPositive
  let endpointMax := min 1 (min (physicalPrecision / (fullMagnitude + 1))
    (phaseTolerance / (4 * (1 + constant) * (fullMagnitude + 1))))
  have endpointPositive : 0 < endpointMax := by dsimp only [endpointMax]; positivity
  have endpointOne : endpointMax ≤ 1 := min_le_left _ _
  have endpointPhysical : endpointMax ≤ physicalPrecision / (fullMagnitude + 1) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have endpointPhase : endpointMax ≤ phaseTolerance / (4 * (1 + constant) * (fullMagnitude + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨endpointMax, endpointPositive, endpointOne, ?_⟩
  filter_upwards [normalizedSeparatingOrbit_eventually_phase_target orbit normalized (by positivity : 0 < phaseTolerance / 8)]
    with incomingTime incomingSmall
  intro scales ratioBound alphaPositive referenceConstant referenceNonnegative threshold scaleRoot boundaryConstant
  filter_upwards [physicalFactory scales ratioBound alphaPositive referenceConstant referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative
      (by positivity : 0 < phaseRadius / 8),
    scales.eventually_uniform_reference_index_rate_small ratioBound alphaPositive referenceNonnegative
      (by positivity : 0 < phaseTolerance / 8), eventually_gt_atTop (0 : ℝ)]
    with frequency physical referenceSmall referenceRate frequencyPositive
  intro phase dipoleAngle rawCap shapeRadius monitor count prepared path prescribed index nonterminal hit hitInside
    origin contact endpoint endpointPositive' endpointBound weakPhysical lift liftContinuous liftInitial liftPolar
  dsimp only
  intro fullProfile exposure sectionBound rotation canonical
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (index.val + 1)
  let growth := 2 * Real.sqrt 2 * omega
  let seed := changed.seed (index.val + 1)
  let fullSize := fun time => prepared.finiteCoordinateSize graph coordinate lift index time +
    ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive ratioPositive _
  have growthPositive : 0 < growth := by dsimp only [growth]; positivity
  have qBound (time : ℝ) (inside : time ∈ Icc 0 hit) :
      seed * Real.exp (growth * (time - origin)) ≤ endpoint :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 origin) growthPositive.le)) seedPositive.le).trans exposure
  have fullEndpoint (time : ℝ) (inside : time ∈ Icc 0 hit) : fullSize time ≤ fullMagnitude * endpoint := by
    have actual := fullProfile time inside
    change fullSize time ≤ fullMagnitude * seed * Real.exp (growth * (time - origin)) at actual
    exact actual.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (qBound time inside) fullNonnegative)
  have physicalBudget : fullMagnitude * endpoint ≤ physicalPrecision := by
    have product := (le_div_iff₀ (by positivity : 0 < fullMagnitude + 1)).mp (endpointBound.trans endpointPhysical)
    nlinarith only [product, endpointPositive']
  have refined := physical prepared path factorPositive index nonterminal hit hitInside weakPhysical lift
    (fun time inside => (fullEndpoint time inside).trans physicalBudget)
  have pairedSmall (side : Fin 2) :
      |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) hit index| +
        |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) hit index| < phaseRadius := by
    fin_cases side
    · exact refined hit ⟨hitInside.1, le_rfl⟩
    · have reference := referenceSmall prepared.toCascadeMaterialPreparedPair hit ⟨hitInside.1, hitInside.2.trans path.stopBound⟩ index
      have extra := abs_nonneg (diagonalDifference prepared.reference hit index / changed.length (index.val + 1) ^ 2 - 1)
      change |unstableShape prepared.reference hit index| + |stableShape prepared.reference hit index| < phaseRadius
      linarith only [reference, extra, phaseRadiusPositive]
  let relativeShape := referenceStraightenedShape motion graph coordinate index hit -
    referenceStraightenedShape prepared.reference graph coordinate index hit
  let relativePhase := relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift
    (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index hit
  have fullNonnegativeAt : 0 ≤ fullSize hit := by
    have := changed.location_pos (index.val + 1)
    dsimp only [fullSize, CascadeSourcePreparedPair.finiteCoordinateSize, CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have dominates : |relativePhase| + (|relativeShape.1| + |relativeShape.2|) ≤ fullSize hit := by
    have extra : 0 ≤ |diagonalDifference motion hit index - diagonalDifference prepared.reference hit index| /
        changed.length (index.val + 1) ^ 2 +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference index hit‖ +
      ‖quadrupoleCenter motion hit index - quadrupoleCenter prepared.reference hit index‖ / changed.location (index.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget hit index patch := by
      have := changed.location_pos (index.val + 1)
      dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
      positivity
    dsimp only [fullSize, CascadeSourcePreparedPair.finiteCoordinateSize, relativeShape, Prod.fst_sub, Prod.snd_sub, relativePhase]
    linarith only [extra]
  have corrections : |relativePhase| + constant * (|relativeShape.1| + |relativeShape.2|) ≤ (1 + constant) * fullSize hit := by
    have scaled := mul_le_mul_of_nonneg_left dominates constantPositive.le
    have phaseScaled := mul_le_mul_of_nonneg_right constantOne (abs_nonneg relativePhase)
    nlinarith only [scaled, phaseScaled, fullNonnegativeAt]
  have phaseBudget : (1 + constant) * (fullMagnitude * endpoint) ≤ phaseTolerance / 4 := by
    have product := (le_div_iff₀ (by positivity : 0 < 4 * (1 + constant) * (fullMagnitude + 1))).mp
      (endpointBound.trans endpointPhase)
    have nonnegative := mul_nonneg constantPositive.le endpointPositive'.le
    nlinarith only [product, endpointPositive', nonnegative]
  have smallCorrections : |relativePhase| + constant * (|relativeShape.1| + |relativeShape.2|) ≤ phaseTolerance / 4 :=
    corrections.trans ((mul_le_mul_of_nonneg_left (fullEndpoint hit ⟨hitInside.1, le_rfl⟩) (by positivity : 0 ≤ 1 + constant)).trans phaseBudget)
  have referenceBound : referenceConstant * (changed.strain + changed.strain ^ 2 + omega⁻¹ ^ 4) < phaseTolerance / 8 := by
    have actual := (referenceRate (index.val + 1)).2
    have identity : omega * (referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)) =
        referenceConstant * (changed.strain + changed.strain ^ 2 + omega⁻¹ ^ 4) := by field_simp; ring
    change omega * (referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)) < phaseTolerance / 8 at actual
    rwa [identity] at actual
  have nonzero : positiveHalfDiagonal motion hit index ≠ 0 := by
    have lower := (path.halfDiagonal_norm_lower hitInside index).1
    have positive := (div_pos (mul_pos factorPositive (changed.length_pos _)) (by norm_num : (0 : ℝ) < 2)).trans_le lower
    exact norm_pos_iff.mp positive
  have rotationPhase := normalizedSeparatingOrbit_matchingRotation_eq_phase_difference orbit normalized incomingTime nonzero
    (liftPolar 0 hit ⟨hitInside.1, le_rfl⟩)
  rw [canonical] at rotationPhase
  obtain ⟨directionIdentity, winding, _, bound⟩ := phaseBounds prepared.toCascadeMaterialPreparedPair path prescribed index nonterminal hit hitInside
    incomingTime contact lift liftContinuous liftInitial liftPolar pairedSmall
  refine ⟨?_, winding, ?_⟩
  · rw [← rotationPhase] at directionIdentity
    exact directionIdentity
  · change |(lift 0 hit - orbit.phase incomingTime + orbit.limitingDipoleAngle) - dipoleAngle (index.val + 1) +
        omega * (contact - changed.predictedTime sectionTime count (index.val + 1)) - (winding : ℝ) * Real.pi| ≤ phaseTolerance
    change _ ≤ |relativePhase| + constant * (|relativeShape.1| + |relativeShape.2|) +
      referenceConstant * (changed.strain + changed.strain ^ 2 + omega⁻¹ ^ 4) +
      |omega * (contact - hit) - (sectionTime - incomingTime)| + |orbit.phase incomingTime + incomingTime| at bound
    linarith only [bound, smallCorrections, referenceBound, sectionBound, incomingSmall, phasePositive]

end EulerNonuniqueness.Paper
