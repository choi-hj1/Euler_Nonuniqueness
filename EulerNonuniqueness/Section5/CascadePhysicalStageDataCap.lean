import EulerNonuniqueness.Section5.CascadePhysicalStageDataMonotonicity
import EulerNonuniqueness.Section5.CascadeSourceCapMonotonicity

noncomputable section
namespace EulerNonuniqueness.Paper.CascadePhysicalStageData

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
  {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant smaller larger : ℝ} {count : ℕ}
  {index : Fin count} {incomingTime extent magnitude coefficient error phaseTolerance timingTolerance matchingTolerance : ℝ}

/-- Return physical stage data to the original prepared pair after enlarging only its cap proofs. -/
def ofEnlargeCap
    (prepared : CascadeSourcePreparedPair smaller scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (bound : smaller ≤ larger) (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    (data : CascadePhysicalStageData (prepared.enlargeCap bound) path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance) :
    CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance := by
  have rawInvariant : (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredInvariant : (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := rfl
  refine {
    entry := data.entry
    entryInside := data.entryInside
    firstSeparation := data.firstSeparation
    direction := data.direction
    directionNorm := data.directionNorm
    outgoingPhase := data.outgoingPhase
    directionPhase := data.directionPhase
    firstError := data.firstError
    secondError := data.secondError
    outgoingProjection := data.outgoingProjection
    centerUpper := data.centerUpper
    extents := data.extents
    domains := data.domains
    sharp := ?_
    winding := data.winding
    wrappedPhase := data.wrappedPhase
    timing := data.timing
    previousMatch := data.previousMatch }
  intro time inside
  simpa only [rawInvariant, centeredInvariant] using data.sharp time inside

@[simp] theorem ofEnlargeCap_entry
    (prepared : CascadeSourcePreparedPair smaller scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (bound : smaller ≤ larger) (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    (data : CascadePhysicalStageData (prepared.enlargeCap bound) path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance) :
    (ofEnlargeCap prepared bound path data).entry = data.entry := rfl

@[simp] theorem ofEnlargeCap_outgoingPhase
    (prepared : CascadeSourcePreparedPair smaller scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (bound : smaller ≤ larger) (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    (data : CascadePhysicalStageData (prepared.enlargeCap bound) path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance) :
    (ofEnlargeCap prepared bound path data).outgoingPhase = data.outgoingPhase := rfl

theorem ofEnlargeCap_direction_winding
    (prepared : CascadeSourcePreparedPair smaller scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (bound : smaller ≤ larger) (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    (data : CascadePhysicalStageData (prepared.enlargeCap bound) path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance) :
    (ofEnlargeCap prepared bound path data).direction = data.direction ∧
      (ofEnlargeCap prepared bound path data).winding = data.winding := ⟨rfl, rfl⟩

/-- Enlarge only the cap proofs of physical stage data on the same actual prepared pair. -/
def toEnlargeCap
    (prepared : CascadeSourcePreparedPair smaller scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (bound : smaller ≤ larger) (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    (data : CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance) :
    CascadePhysicalStageData (prepared.enlargeCap bound) path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance := by
  have rawInvariant : (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredInvariant : (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := rfl
  refine {
    entry := data.entry
    entryInside := data.entryInside
    firstSeparation := data.firstSeparation
    direction := data.direction
    directionNorm := data.directionNorm
    outgoingPhase := data.outgoingPhase
    directionPhase := data.directionPhase
    firstError := data.firstError
    secondError := data.secondError
    outgoingProjection := data.outgoingProjection
    centerUpper := data.centerUpper
    extents := data.extents
    domains := data.domains
    sharp := ?_
    winding := data.winding
    wrappedPhase := data.wrappedPhase
    timing := data.timing
    previousMatch := data.previousMatch }
  intro time inside
  simpa only [rawInvariant, centeredInvariant] using data.sharp time inside

@[simp] theorem toEnlargeCap_entry
    (prepared : CascadeSourcePreparedPair smaller scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (bound : smaller ≤ larger) (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    (data : CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance) :
    (toEnlargeCap prepared bound path data).entry = data.entry := rfl

@[simp] theorem toEnlargeCap_outgoingPhase
    (prepared : CascadeSourcePreparedPair smaller scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (bound : smaller ≤ larger) (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    (data : CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance) :
    (toEnlargeCap prepared bound path data).outgoingPhase = data.outgoingPhase := rfl

theorem toEnlargeCap_direction_winding
    (prepared : CascadeSourcePreparedPair smaller scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (bound : smaller ≤ larger) (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    (data : CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance) :
    (toEnlargeCap prepared bound path data).direction = data.direction ∧
      (toEnlargeCap prepared bound path data).winding = data.winding := ⟨rfl, rfl⟩

end EulerNonuniqueness.Paper.CascadePhysicalStageData
