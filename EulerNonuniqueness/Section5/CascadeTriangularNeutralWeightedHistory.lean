import EulerNonuniqueness.Section5.CascadeCorrectedPhaseOriginalHistory
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect
import EulerNonuniqueness.Section5.CascadeDilationClosedPhysicalHistory
import EulerNonuniqueness.General.TriangularNeutralWeightedHistory

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_triangular_neutral_weighted_history
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateZero : coordinate 0 = 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {scaleRoot boundaryConstant factor threshold referenceConstant : ℝ},
    0 < scaleRoot → 0 ≤ boundaryConstant → 0 < factor → factor ≤ 1 / 8 →
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {shapeRadius monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∃ lift : Fin 2 → ℝ → ℝ,
      (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift side time : ℂ))) ∧
      ∀ weight : ℝ, 0 < weight →
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let dilation := fun time => (diagonalDifference first time index - diagonalDifference second time index) /
        changed.length (index.val + 1) ^ 2
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * |dilation time|) ≤
          (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
            |relativeDilationPhysicalVelocity changed first second index time|) / weight ∧
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared) index time|) ≤
        |changed.omega (index.val + 1)| / weight ^ 2 *
          (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
            |relativeDilationPhysicalVelocity changed first second index time|) +
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
          |relativeCorrectedPaperPhaseVelocity changed (phaseCorrection 1 graph) (cascadePairedMotion prepared) index time -
            changed.omega (index.val + 1) * dilation time|) / weight := by
  obtain ⟨_, _, phaseRadius, phasePositive, phaseQuarter, phaseFactory⟩ :=
    exists_uniform_cascade_sameGraph_corrected_phase_lift_jet graphAnalytic graphZero graphDerivative
      coordinateZero coordinateDerivative
  obtain ⟨correctionSmooth, _, _, _, _, _, _, _⟩ :=
    sameGraph_phaseCorrection_exists_uniform_stable_factor graphAnalytic graphZero graphDerivative
      coordinateZero coordinateDerivative
  obtain ⟨smoothRadius, smoothPositive, smoothInside⟩ := Metric.mem_nhds_iff.mp
    (correctionSmooth.eventually (by norm_num))
  let baseRadius := min phaseRadius smoothRadius
  let radius := baseRadius / 2
  have basePositive : 0 < baseRadius := lt_min phasePositive smoothPositive
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusBase : radius < baseRadius := by dsimp only [radius]; linarith
  have baseQuarter : baseRadius ≤ 1 / 4 := (min_le_left _ _).trans phaseQuarter
  refine ⟨radius, radiusPositive, radiusBase.le.trans baseQuarter, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative
  filter_upwards [phaseFactory scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      factorPositive factorSmall thresholdSmall referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative basePositive,
    scales.eventually_cascade_dilation_closed_physical_history amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative factorPositive]
    with frequency actualPhase referenceSmall actualDilation
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishNonnegative finishBound small
  let changed : Scales := {scales with frequency := frequency}
  let correction := phaseCorrection 1 graph
  have pairedSmall (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| < baseRadius := by
    fin_cases side
    · exact (small time inside).trans_lt radiusBase
    · have sharp := referenceSmall prepared time
        (show time ∈ Icc (0 : ℝ) 1 from ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩) index
      change |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < baseRadius
      linarith [abs_nonneg (diagonalDifference prepared.reference time index / changed.length (index.val + 1) ^ 2 - 1)]
  obtain ⟨lift, liftContinuous, initial, polar, phaseJet, physicalPhaseJet, _⟩ :=
    actualPhase prepared path index nonterminal finish finishNonnegative finishBound
      (fun side time inside => (pairedSmall side time inside).trans_le (min_le_left _ _))
  refine ⟨lift, liftContinuous, polar, ?_⟩
  let dilation := fun time => (diagonalDifference prepared.trajectory.movingFamily.patchMotion time index -
    diagonalDifference prepared.reference time index) / changed.length (index.val + 1) ^ 2
  let dilationVelocity := fun time =>
    (prepared.pairedDiagonalVelocity 0 index time - prepared.pairedDiagonalVelocity 1 index time) /
      changed.length (index.val + 1) ^ 2
  let corrected := relativeCorrectedPaperPhase correction lift (cascadePairedMotion prepared) index
  let phaseVelocity := fun time =>
    geometricCorrectedPhaseVelocity correction (cascadePairedMotion prepared 0) index time -
      geometricCorrectedPhaseVelocity correction (cascadePairedMotion prepared 1) index time
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 finish) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, finishBound, path.stopBound]⟩
  have rawSmall (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| ≤ 1 / 4 :=
    (pairedSmall side time inside).le.trans baseQuarter
  have smooth (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      ContDiffAt ℝ 2 correction (unstableShape (cascadePairedMotion prepared side) time index) := by
    apply smoothInside
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans_lt
      ((pairedSmall side time inside).trans_le (min_le_right _ _))
  have geometricDerivative (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      HasDerivAt (correctedPaperPhase correction (lift side) (cascadePairedMotion prepared side) index)
        (geometricCorrectedPhaseVelocity correction (cascadePairedMotion prepared side) index time) time := by
    have localSmall := rawSmall side time inside
    have localSmooth := (smooth side time inside).differentiableAt (by norm_num)
    have localJet := phaseJet side time inside
    fin_cases side
    · exact prepared.trajectory.movingFamily.correctedPaperPhase_hasDerivAt_geometric _ _ index
        (fun _ => globalInside time inside) localSmall localSmooth localJet
    · simp only [cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] at localSmall localSmooth localJet ⊢
      exact prepared.referenceWitness.trajectory.movingFamily.correctedPaperPhase_hasDerivAt_geometric _ _ index
        (fun _ => globalInside time inside) localSmall localSmooth localJet
  have geometricContinuous (side : Fin 2) : ContinuousOn
      (geometricCorrectedPhaseVelocity correction (cascadePairedMotion prepared side) index) (Icc 0 finish) := by
    have localSmall := rawSmall side
    have localSmooth := smooth side
    fin_cases side
    · exact prepared.trajectory.movingFamily.geometricCorrectedPhaseVelocity_continuousOn _ index
        (fun time inside _ => globalInside time inside) localSmall localSmooth
    · simp only [cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] at localSmall localSmooth ⊢
      exact prepared.referenceWitness.trajectory.movingFamily.geometricCorrectedPhaseVelocity_continuousOn _ index
        (fun time inside _ => globalInside time inside) localSmall localSmooth
  have dilationDerivative (time : ℝ) (inside : time ∈ Icc 0 finish) :
      HasDerivAt dilation (dilationVelocity time) time := by
    have actual := ((prepared.paired_diagonal_hasDerivAt 0 index (globalInside time inside)).sub
      (prepared.paired_diagonal_hasDerivAt 1 index (globalInside time inside))).div_const (changed.length (index.val + 1) ^ 2)
    exact actual
  have correctedDerivative (time : ℝ) (inside : time ∈ Icc 0 finish) :
      HasDerivAt corrected (phaseVelocity time) time :=
    (geometricDerivative 0 time inside).sub (geometricDerivative 1 time inside)
  have dilationContinuous : ContinuousOn dilation (Icc 0 finish) :=
    fun time inside => (dilationDerivative time inside).continuousAt.continuousWithinAt
  have correctedContinuous : ContinuousOn corrected (Icc 0 finish) :=
    fun time inside => (correctedDerivative time inside).continuousAt.continuousWithinAt
  have dilationVelocityContinuous : Continuous dilationVelocity :=
    ((prepared.pairedDiagonalVelocity_continuous 0 index).sub
      (prepared.pairedDiagonalVelocity_continuous 1 index)).div_const _
  have phaseVelocityContinuous : ContinuousOn phaseVelocity (Icc 0 finish) :=
    (geometricContinuous 0).sub (geometricContinuous 1)
  have dilationPhysical (time : ℝ) (inside : time ∈ Icc 0 finish) :
      dilationVelocity time = relativeDilationPhysicalVelocity changed prepared.trajectory.movingFamily.patchMotion prepared.reference index time :=
    (dilationDerivative time inside).unique
      (actualDilation prepared path index nonterminal time ⟨inside.1, inside.2.trans finishBound⟩).1
  have phasePhysical (time : ℝ) (inside : time ∈ Ioo 0 finish) :
      phaseVelocity time = relativeCorrectedPaperPhaseVelocity changed correction (cascadePairedMotion prepared) index time :=
    (correctedDerivative time ⟨inside.1.le, inside.2.le⟩).unique (physicalPhaseJet time inside)
  have dilationInitial : dilation 0 = 0 := by
    have actual := (actualDilation prepared path index nonterminal 0 ⟨le_rfl, path.stopPositive.le⟩).2
    simpa only [intervalIntegral.integral_same] using actual
  intro weight weightPositive
  let source := fun time => |dilationVelocity time|
  let phaseSource := fun time => |phaseVelocity time - changed.omega (index.val + 1) * dilation time|
  have sourceContinuous : ContinuousOn source (Icc 0 finish) := dilationVelocityContinuous.abs.continuousOn
  have phaseSourceContinuous : ContinuousOn phaseSource (Icc 0 finish) :=
    (phaseVelocityContinuous.sub (continuousOn_const.mul dilationContinuous)).abs
  have phaseBound (time : ℝ) (inside : time ∈ Ioo 0 finish) :
      |phaseVelocity time| ≤ |changed.omega (index.val + 1)| * |dilation time| + phaseSource time := by
    have triangle := abs_add (changed.omega (index.val + 1) * dilation time)
      (phaseVelocity time - changed.omega (index.val + 1) * dilation time)
    have identity : changed.omega (index.val + 1) * dilation time +
        (phaseVelocity time - changed.omega (index.val + 1) * dilation time) = phaseVelocity time := by ring
    rw [identity, abs_mul] at triangle
    exact triangle
  have weighted := EulerNonuniqueness.General.triangular_neutral_weighted_history finishNonnegative weightPositive
    (abs_nonneg (changed.omega (index.val + 1))) dilationContinuous dilationInitial correctedContinuous initial
    sourceContinuous phaseSourceContinuous (fun _ _ => abs_nonneg _) (fun _ _ => abs_nonneg _)
    (fun time inside => dilationDerivative time ⟨inside.1.le, inside.2.le⟩)
    (fun time inside => correctedDerivative time ⟨inside.1.le, inside.2.le⟩)
    (fun _ _ => le_rfl) phaseBound
  have sourceIntegral :
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * source time) =
        ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
          |relativeDilationPhysicalVelocity changed prepared.trajectory.movingFamily.patchMotion prepared.reference index time| := by
    apply intervalIntegral.integral_congr
    intro time inside
    rw [uIcc_of_le finishNonnegative] at inside
    change Real.exp (-weight * time) * |dilationVelocity time| = _
    rw [dilationPhysical time inside]
  have phaseIntegral :
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * phaseSource time) =
        ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
          |relativeCorrectedPaperPhaseVelocity changed correction (cascadePairedMotion prepared) index time -
            changed.omega (index.val + 1) * dilation time| := by
    apply intervalIntegral.integral_congr_ae
    have almostDifferent : ∀ᵐ time : ℝ ∂volume, time ≠ finish := by simp [ae_iff]
    filter_upwards [almostDifferent] with time different
    intro inside
    rw [uIoc_of_le finishNonnegative] at inside
    have interior : time ∈ Ioo 0 finish := ⟨inside.1, lt_of_le_of_ne inside.2 different⟩
    change Real.exp (-weight * time) * |phaseVelocity time - changed.omega (index.val + 1) * dilation time| = _
    rw [phasePhysical time interior]
  rw [sourceIntegral, phaseIntegral] at weighted
  exact weighted

end EulerNonuniqueness.Paper
