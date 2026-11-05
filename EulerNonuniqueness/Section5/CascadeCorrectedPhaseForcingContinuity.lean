import EulerNonuniqueness.Section6.PaperCorrectedPhaseForcingContinuity
import EulerNonuniqueness.Section5.CascadePairedSaddleAdmissibility
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect
import EulerNonuniqueness.Section4.UniversalReferenceMechanicalData
import EulerNonuniqueness.Section6.SameGraphPhaseCorrection

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_corrected_phase_forcing_continuity
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
    ∀ index : Fin count, ∀ finish : ℝ, 0 < finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∀ side : Fin 2, ContinuousOn (correctedPaperPhaseForcing {scales with frequency := frequency}
      (phaseCorrection 1 graph) (cascadePairedMotion prepared side) index) (Icc 0 finish) := by
  obtain ⟨correctionSmooth, _, _, _, _, _, _, _⟩ :=
    sameGraph_phaseCorrection_exists_uniform_stable_factor graphAnalytic graphZero graphDerivative
      coordinateZero coordinateDerivative
  obtain ⟨smoothRadius, smoothPositive, smoothInside⟩ := Metric.mem_nhds_iff.mp
    (correctionSmooth.eventually (by norm_num))
  let radius := min (smoothRadius / 2) (1 / 4)
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusQuarter : radius ≤ 1 / 4 := min_le_right _ _
  have radiusSmooth : radius < smoothRadius := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨radius, radiusPositive, radiusQuarter, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_cascade_paired_saddle_admissible amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      factorPositive (factorSmall.trans (by norm_num)) thresholdSmall referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative radiusPositive,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative]
    with frequency frequencyPositive admissible referenceSmall mechanical
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index finish finishPositive finishBound small side
  let changed : Scales := {scales with frequency := frequency}
  have actual := admissible prepared path
  have fullInside (time : ℝ) (inside : time ∈ Icc 0 finish) : time ∈ Icc 0 path.stop :=
    ⟨inside.1, inside.2.trans finishBound⟩
  have pairedRaw (currentSide : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared currentSide) time index| +
        |stableShape (cascadePairedMotion prepared currentSide) time index| ≤ radius := by
    fin_cases currentSide
    · exact small time inside
    · have sharp := referenceSmall prepared time
        (show time ∈ Icc (0 : ℝ) 1 from ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩) index
      change |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| ≤ radius
      linarith [abs_nonneg (diagonalDifference prepared.reference time index / changed.length (index.val + 1) ^ 2 - 1)]
  have smooth (currentSide : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      ContDiffAt ℝ 2 (phaseCorrection 1 graph) (unstableShape (cascadePairedMotion prepared currentSide) time index) := by
    apply smoothInside
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans_lt
      ((pairedRaw currentSide time inside).trans_lt radiusSmooth)
  have noncollision (currentSide : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      FourPointNoncollision (fun patch => patchCentroid (cascadePairedMotion prepared currentSide) time index patch) := by
    fin_cases currentSide
    · intro first second different collision
      change patchCentroid prepared.trajectory.movingFamily.patchMotion time index first -
        patchCentroid prepared.trajectory.movingFamily.patchMotion time index second = 0 at collision
      have gap := path.internal_centroid_gap (fullInside time inside) index first second (Ne.symm different)
      rw [collision, norm_zero] at gap
      exact (mul_pos factorPositive (changed.length_pos _)).not_le gap
    · simp only [cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity]
      have referenceInside : time ∈ Icc (0 : ℝ) 2 :=
        ⟨inside.1, by linarith [inside.2, finishBound, path.stopBound]⟩
      have data := mechanical prepared.referenceWitness.trajectory.movingFamily.patchMotion
        prepared.referenceWitness.evolution prepared.referenceWitness.coarse time referenceInside index
      intro first second different collision
      change patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time index first -
        patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time index second = 0 at collision
      have gap := data.1.internalSeparated first second different
      rw [collision, norm_zero] at gap
      exact (div_pos (changed.length_pos _) (by norm_num : (0 : ℝ) < 100)).not_le gap
  exact ((actual.1 side).mono finishBound).correctedPaperPhaseForcing_continuousOn_of_boundary_gaps finishPositive
    amplitudePositive frequencyPositive (by change 0 < scales.ratio; linarith) actual.2.1
    (fun time inside => actual.2.2.1 side time (fullInside time inside))
    (fun time inside => actual.2.2.2 side time (fullInside time inside))
    (phaseCorrection 1 graph) index (noncollision side)
    (fun time inside => (pairedRaw side time inside).trans radiusQuarter) (smooth side)

end EulerNonuniqueness.Paper
