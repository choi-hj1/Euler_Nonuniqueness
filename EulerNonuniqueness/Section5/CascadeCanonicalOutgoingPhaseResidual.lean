import EulerNonuniqueness.Section5.CascadeCorrectedPhaseDynamics
import EulerNonuniqueness.General.ComplexPhaseUniqueness

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem CascadeMaterialPreparedPair.canonical_outgoing_phase_residual
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
    {count : ℕ}
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared)
    (prescribed : PrescribedCascadePhases scales orbit sectionTime count phase dipoleAngle)
    (graph : ℝ → ℝ) (index : Fin count) (nonterminal : index.val + 1 < count)
    (hit : ℝ) (hitInside : hit ∈ Icc 0 path.stop) (incomingTime contact : ℝ)
    (lift : Fin 2 → ℝ → ℝ)
    (liftContinuous : ∀ side, ContinuousOn (lift side) (Icc 0 hit))
    (liftInitial : ∀ side, lift side 0 = phase (index.val + 1))
    (liftPolar : ∀ side, ∀ time ∈ Icc 0 hit,
      positiveHalfDiagonal (cascadePairedMotion prepared side) time index =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared side) time index‖ : ℂ) *
          Complex.exp (Complex.I * (lift side time : ℂ)))
    (rotation : ℂ)
    (rotationIdentity : rotation =
      Complex.exp (Complex.I * ((lift 0 hit - orbit.phase incomingTime : ℝ) : ℂ))) :
    let outgoingPhase := lift 0 hit - orbit.phase incomingTime + orbit.limitingDipoleAngle
    let timingShift := scales.omega (index.val + 1) *
      (contact - scales.predictedTime sectionTime count (index.val + 1))
    let relativePhase := relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift
      (cascadePairedMotion prepared) index hit
    let angleCorrection := (Real.sqrt 2 - 1) / 4 *
      (shapeChartAngle (unstableShape (cascadePairedMotion prepared 0) hit index,
        stableShape (cascadePairedMotion prepared 0) hit index) -
      shapeChartAngle (unstableShape (cascadePairedMotion prepared 1) hit index,
        stableShape (cascadePairedMotion prepared 1) hit index))
    let graphCorrection :=
      phaseCorrection 1 graph (unstableShape (cascadePairedMotion prepared 0) hit index) -
      phaseCorrection 1 graph (unstableShape (cascadePairedMotion prepared 1) hit index)
    let referenceDrift := lift 1 hit - phase (index.val + 1) +
      scales.omega (index.val + 1) * hit
    let sectionError := scales.omega (index.val + 1) * (contact - hit) -
      (sectionTime - incomingTime)
    Complex.exp (Complex.I * (outgoingPhase : ℂ)) =
      rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ)) ∧
    ∃ winding : ℤ,
      outgoingPhase - dipoleAngle (index.val + 1) + timingShift -
          (winding : ℝ) * Real.pi =
        relativePhase + angleCorrection + graphCorrection + referenceDrift + sectionError -
          (orbit.phase incomingTime + incomingTime) ∧
      |outgoingPhase - dipoleAngle (index.val + 1) + timingShift -
          (winding : ℝ) * Real.pi| ≤
        |relativePhase| + |angleCorrection| + |graphCorrection| +
          referenceConstant * (scales.strain + scales.strain ^ 2 +
            (scales.omega (index.val + 1))⁻¹ ^ 4) +
          |sectionError| + |orbit.phase incomingTime + incomingTime| := by
  dsimp only
  let outgoingPhase := lift 0 hit - orbit.phase incomingTime + orbit.limitingDipoleAngle
  let timingShift := scales.omega (index.val + 1) *
    (contact - scales.predictedTime sectionTime count (index.val + 1))
  let relativePhase := relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift
    (cascadePairedMotion prepared) index hit
  let angleCorrection := (Real.sqrt 2 - 1) / 4 *
    (shapeChartAngle (unstableShape (cascadePairedMotion prepared 0) hit index,
      stableShape (cascadePairedMotion prepared 0) hit index) -
    shapeChartAngle (unstableShape (cascadePairedMotion prepared 1) hit index,
      stableShape (cascadePairedMotion prepared 1) hit index))
  let graphCorrection :=
    phaseCorrection 1 graph (unstableShape (cascadePairedMotion prepared 0) hit index) -
    phaseCorrection 1 graph (unstableShape (cascadePairedMotion prepared 1) hit index)
  let referenceDrift := lift 1 hit - phase (index.val + 1) +
    scales.omega (index.val + 1) * hit
  let sectionError := scales.omega (index.val + 1) * (contact - hit) -
    (sectionTime - incomingTime)
  change Complex.exp (Complex.I * (outgoingPhase : ℂ)) = _ ∧ ∃ winding : ℤ, _
  have hitOne : hit ≤ 1 := hitInside.2.trans path.stopBound
  have referenceInside (time : ℝ) (inside : time ∈ Icc 0 hit) :
      time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith only [inside.2, hitOne]⟩
  obtain ⟨unstable, referenceLift, initial, referencePolar, evolution, coarse, sharp⟩ :=
    prepared.referenceSolution
  have referenceNonzero (time : ℝ) (inside : time ∈ Icc 0 hit) :
      positiveHalfDiagonal prepared.reference time index ≠ 0 := by
    have lower := (coarse.2.1 time (referenceInside time inside) index).2.2.1
    have scaled := (le_div_iff₀ (sq_pos_of_pos (scales.length_pos (index.val + 1)))).mp lower
    have differencePositive : 0 < diagonalDifference prepared.reference time index := by
      nlinarith only [scaled, sq_pos_of_pos (scales.length_pos (index.val + 1))]
    intro zero
    change 0 < ‖positiveHalfDiagonal prepared.reference time index‖ ^ 2 -
      ‖negativeHalfDiagonal prepared.reference time index‖ ^ 2 at differencePositive
    rw [zero, norm_zero] at differencePositive
    nlinarith only [differencePositive, sq_nonneg ‖negativeHalfDiagonal prepared.reference time index‖]
  have referenceEquality : EqOn (lift 1) (fun time => referenceLift time index) (Icc 0 hit) := by
    apply General.phase_polar_lift_unique_on_Icc hitInside.1 (liftContinuous 1)
      ((referencePolar index).1.mono (fun time inside => referenceInside time inside))
      ((liftInitial 1).trans (referencePolar index).2.1.symm) referenceNonzero
    · intro time inside
      simpa only [cascadePairedMotion, Fin.cases_succ] using liftPolar 1 time inside
    · intro time inside
      exact (referencePolar index).2.2 time (referenceInside time inside)
  have referenceBound : |referenceDrift| ≤
      referenceConstant * (scales.strain + scales.strain ^ 2 +
        (scales.omega (index.val + 1))⁻¹ ^ 4) := by
    dsimp only [referenceDrift]
    rw [referenceEquality ⟨hitInside.1, le_rfl⟩]
    simpa only [one_mul, mul_one] using
      (sharp.1 1 (by norm_num) le_rfl hit ⟨hitInside.1, hitOne⟩ index).2
  refine ⟨?_, ?_⟩
  · rw [rotationIdentity, ← Complex.exp_add]
    congr 1
    dsimp only [outgoingPhase]
    push_cast
    ring
  · obtain ⟨winding, windingIdentity⟩ :=
      (prescribed (index.val + 1) (by omega) nonterminal).2
    have identity : outgoingPhase - dipoleAngle (index.val + 1) + timingShift -
        ((-winding : ℤ) : ℝ) * Real.pi =
        relativePhase + angleCorrection + graphCorrection + referenceDrift + sectionError -
          (orbit.phase incomingTime + incomingTime) := by
      dsimp only [outgoingPhase, timingShift, relativePhase, angleCorrection,
        graphCorrection, referenceDrift, sectionError, relativeCorrectedPaperPhase,
        correctedPaperPhase]
      push_cast
      linear_combination -windingIdentity
    refine ⟨-winding, identity, ?_⟩
    rw [identity]
    calc
      |relativePhase + angleCorrection + graphCorrection + referenceDrift + sectionError -
          (orbit.phase incomingTime + incomingTime)| ≤
          |relativePhase + angleCorrection + graphCorrection + referenceDrift + sectionError| +
            |orbit.phase incomingTime + incomingTime| := abs_sub _ _
      _ ≤ |relativePhase| + |angleCorrection| + |graphCorrection| + |referenceDrift| +
          |sectionError| + |orbit.phase incomingTime + incomingTime| := by
        have first := abs_add relativePhase angleCorrection
        have second := abs_add (relativePhase + angleCorrection) graphCorrection
        have third := abs_add (relativePhase + angleCorrection + graphCorrection) referenceDrift
        have fourth := abs_add
          (relativePhase + angleCorrection + graphCorrection + referenceDrift) sectionError
        linarith only [first, second, third, fourth]
      _ ≤ _ := by
        dsimp only [relativePhase, angleCorrection, graphCorrection, sectionError]
        linarith only [referenceBound]

end EulerNonuniqueness.Paper
