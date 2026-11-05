import EulerNonuniqueness.Section5.CascadeCanonicalOutgoingPhaseResidual
import EulerNonuniqueness.Section6.NormalFormPhaseCorrectionBound

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_canonical_outgoing_phase_coordinate_bound
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
    ∀ {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
      {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    PrescribedCascadePhases scales orbit sectionTime count phase dipoleAngle →
    ∀ index : Fin count, index.val + 1 < count → ∀ hit ∈ Icc 0 path.stop,
    ∀ incomingTime contact : ℝ, ∀ lift : Fin 2 → ℝ → ℝ,
    (∀ side, ContinuousOn (lift side) (Icc 0 hit)) →
    (∀ side, lift side 0 = phase (index.val + 1)) →
    (∀ side, ∀ time ∈ Icc 0 hit,
      positiveHalfDiagonal (cascadePairedMotion prepared side) time index =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared side) time index‖ : ℂ) *
          Complex.exp (Complex.I * (lift side time : ℂ))) →
    (∀ side : Fin 2,
      |unstableShape (cascadePairedMotion prepared side) hit index| +
        |stableShape (cascadePairedMotion prepared side) hit index| < radius) →
    let rotation := Complex.exp (Complex.I * ((lift 0 hit - orbit.phase incomingTime : ℝ) : ℂ))
    let outgoingPhase := lift 0 hit - orbit.phase incomingTime + orbit.limitingDipoleAngle
    let timingShift := scales.omega (index.val + 1) *
      (contact - scales.predictedTime sectionTime count (index.val + 1))
    let relativePhase := relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift
      (cascadePairedMotion prepared) index hit
    let relativeShape := referenceStraightenedShape (cascadePairedMotion prepared 0) graph coordinate index hit -
      referenceStraightenedShape (cascadePairedMotion prepared 1) graph coordinate index hit
    let angleCorrection := (Real.sqrt 2 - 1) / 4 *
      (shapeChartAngle (unstableShape (cascadePairedMotion prepared 0) hit index,
        stableShape (cascadePairedMotion prepared 0) hit index) -
      shapeChartAngle (unstableShape (cascadePairedMotion prepared 1) hit index,
        stableShape (cascadePairedMotion prepared 1) hit index))
    let graphCorrection := phaseCorrection 1 graph (unstableShape (cascadePairedMotion prepared 0) hit index) -
      phaseCorrection 1 graph (unstableShape (cascadePairedMotion prepared 1) hit index)
    let referenceDrift := lift 1 hit - phase (index.val + 1) + scales.omega (index.val + 1) * hit
    let sectionError := scales.omega (index.val + 1) * (contact - hit) - (sectionTime - incomingTime)
    Complex.exp (Complex.I * (outgoingPhase : ℂ)) =
      rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ)) ∧
    ∃ winding : ℤ,
      outgoingPhase - dipoleAngle (index.val + 1) + timingShift - (winding : ℝ) * Real.pi =
        relativePhase + angleCorrection + graphCorrection + referenceDrift + sectionError -
          (orbit.phase incomingTime + incomingTime) ∧
      |outgoingPhase - dipoleAngle (index.val + 1) + timingShift - (winding : ℝ) * Real.pi| ≤
        |relativePhase| + constant * (|relativeShape.1| + |relativeShape.2|) +
          referenceConstant * (scales.strain + scales.strain ^ 2 + (scales.omega (index.val + 1))⁻¹ ^ 4) +
          |sectionError| + |orbit.phase incomingTime + incomingTime| := by
  obtain ⟨radius, radiusPositive, constant, constantOne, correctionEstimate⟩ :=
    localNormalFormChart_exists_uniform_phase_correction_bound graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  refine ⟨radius, radiusPositive, constant, constantOne, ?_⟩
  intro scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count
    prepared path prescribed index nonterminal hit hitInside incomingTime contact lift liftContinuous liftInitial liftPolar small
  dsimp only
  let rotation := Complex.exp (Complex.I * ((lift 0 hit - orbit.phase incomingTime : ℝ) : ℂ))
  let outgoingPhase := lift 0 hit - orbit.phase incomingTime + orbit.limitingDipoleAngle
  let timingShift := scales.omega (index.val + 1) *
    (contact - scales.predictedTime sectionTime count (index.val + 1))
  let relativePhase := relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift
    (cascadePairedMotion prepared) index hit
  let relativeShape := referenceStraightenedShape (cascadePairedMotion prepared 0) graph coordinate index hit -
    referenceStraightenedShape (cascadePairedMotion prepared 1) graph coordinate index hit
  let angleCorrection := (Real.sqrt 2 - 1) / 4 *
    (shapeChartAngle (unstableShape (cascadePairedMotion prepared 0) hit index,
      stableShape (cascadePairedMotion prepared 0) hit index) -
    shapeChartAngle (unstableShape (cascadePairedMotion prepared 1) hit index,
      stableShape (cascadePairedMotion prepared 1) hit index))
  let graphCorrection := phaseCorrection 1 graph (unstableShape (cascadePairedMotion prepared 0) hit index) -
    phaseCorrection 1 graph (unstableShape (cascadePairedMotion prepared 1) hit index)
  let sectionError := scales.omega (index.val + 1) * (contact - hit) - (sectionTime - incomingTime)
  have actual := prepared.canonical_outgoing_phase_residual path prescribed graph index nonterminal hit hitInside incomingTime contact
    lift liftContinuous liftInitial liftPolar rotation rfl
  dsimp only at actual
  obtain ⟨rotationIdentity, winding, windingIdentity, residualBound⟩ := actual
  have corrections : |angleCorrection| + |graphCorrection| ≤ constant * (|relativeShape.1| + |relativeShape.2|) := by
    simpa only [angleCorrection, graphCorrection, relativeShape, referenceStraightenedShape,
      Prod.fst_sub, Prod.snd_sub] using
      correctionEstimate
        (unstableShape (cascadePairedMotion prepared 0) hit index, stableShape (cascadePairedMotion prepared 0) hit index)
        (unstableShape (cascadePairedMotion prepared 1) hit index, stableShape (cascadePairedMotion prepared 1) hit index)
        (small 0) (small 1)
  refine ⟨rotationIdentity, winding, windingIdentity, ?_⟩
  change |outgoingPhase - dipoleAngle (index.val + 1) + timingShift - (winding : ℝ) * Real.pi| ≤
    |relativePhase| + constant * (|relativeShape.1| + |relativeShape.2|) +
      referenceConstant * (scales.strain + scales.strain ^ 2 + (scales.omega (index.val + 1))⁻¹ ^ 4) +
      |sectionError| + |orbit.phase incomingTime + incomingTime|
  change |outgoingPhase - dipoleAngle (index.val + 1) + timingShift - (winding : ℝ) * Real.pi| ≤
    |relativePhase| + |angleCorrection| + |graphCorrection| +
      referenceConstant * (scales.strain + scales.strain ^ 2 + (scales.omega (index.val + 1))⁻¹ ^ 4) +
      |sectionError| + |orbit.phase incomingTime + incomingTime| at residualBound
  linarith only [residualBound, corrections]

end EulerNonuniqueness.Paper
