import EulerNonuniqueness.Section5.CascadePhysicalStageData

noncomputable section
open Set
namespace EulerNonuniqueness.Paper.CascadePhysicalStageData

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
  {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant rawCap : ℝ} {count : ℕ}
  {prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
    threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count}
  {path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair} {index : Fin count}
  {incomingTime extent magnitude coefficient error phaseTolerance timingTolerance matchingTolerance : ℝ}
  {largerExtent largerMagnitude largerPhaseTolerance largerTimingTolerance largerMatchingTolerance : ℝ}

/-- Enlarge physical budgets while preserving the trajectory, entry, phase, and all actual witnesses. -/
def weakenBounds
    (data : CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance)
    (extentBound : extent ≤ largerExtent) (magnitudeBound : magnitude ≤ largerMagnitude)
    (phaseBound : phaseTolerance ≤ largerPhaseTolerance) (timingBound : timingTolerance ≤ largerTimingTolerance)
    (matchingBound : matchingTolerance ≤ largerMatchingTolerance) :
    CascadePhysicalStageData prepared path index incomingTime largerExtent largerMagnitude coefficient error
      largerPhaseTolerance largerTimingTolerance largerMatchingTolerance where
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
  extents := by
    intro time inside patch
    have bound := mul_le_mul_of_nonneg_right extentBound (scales.length_pos (index.val + 1)).le
    exact ⟨((data.extents time inside patch).1).trans bound, ((data.extents time inside patch).2).trans bound⟩
  domains := by
    intro time inside patch
    have bound := mul_le_mul_of_nonneg_right extentBound (scales.length_pos (index.val + 1)).le
    exact ⟨((data.domains time inside patch).1).trans (Metric.closedBall_subset_closedBall bound),
      ((data.domains time inside patch).2).trans (Metric.closedBall_subset_closedBall bound)⟩
  sharp := by
    intro time inside
    exact (data.sharp time inside).trans (mul_le_mul_of_nonneg_right magnitudeBound (Real.exp_pos _).le)
  winding := data.winding
  wrappedPhase := data.wrappedPhase.trans phaseBound
  timing := data.timing.trans timingBound
  previousMatch := by
    intro nonterminal
    obtain ⟨hit, inside, rotation, rotationNorm, matching⟩ := data.previousMatch nonterminal
    exact ⟨hit, inside, rotation, rotationNorm, matching.trans matchingBound⟩

@[simp] theorem weakenBounds_entry
    (data : CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance)
    (extentBound : extent ≤ largerExtent) (magnitudeBound : magnitude ≤ largerMagnitude)
    (phaseBound : phaseTolerance ≤ largerPhaseTolerance) (timingBound : timingTolerance ≤ largerTimingTolerance)
    (matchingBound : matchingTolerance ≤ largerMatchingTolerance) :
    (data.weakenBounds extentBound magnitudeBound phaseBound timingBound matchingBound).entry = data.entry := rfl

@[simp] theorem weakenBounds_direction
    (data : CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance)
    (extentBound : extent ≤ largerExtent) (magnitudeBound : magnitude ≤ largerMagnitude)
    (phaseBound : phaseTolerance ≤ largerPhaseTolerance) (timingBound : timingTolerance ≤ largerTimingTolerance)
    (matchingBound : matchingTolerance ≤ largerMatchingTolerance) :
    (data.weakenBounds extentBound magnitudeBound phaseBound timingBound matchingBound).direction = data.direction := rfl

end EulerNonuniqueness.Paper.CascadePhysicalStageData
