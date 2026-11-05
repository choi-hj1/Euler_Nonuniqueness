import EulerNonuniqueness.Section5.CascadeCorrectedPhaseLiftJet
import EulerNonuniqueness.Section6.MovingCorrectedPhaseHistory

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_sameGraph_corrected_phase_original_history
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
    (∀ side, ∀ time ∈ Icc 0 finish,
      |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| < radius) →
    ∃ lift : Fin 2 → ℝ → ℝ,
      (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift side time : ℂ))) ∧
      ∀ time ∈ Icc 0 finish,
        relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared) index time =
          ∫ current in (0 : ℝ)..time,
            relativeCorrectedPaperPhaseVelocity {scales with frequency := frequency} (phaseCorrection 1 graph)
              (cascadePairedMotion prepared) index current := by
  obtain ⟨_, _, phaseRadius, phasePositive, phaseSmall, phaseFactory⟩ :=
    exists_uniform_cascade_sameGraph_corrected_phase_lift_jet graphAnalytic graphZero graphDerivative
      coordinateZero coordinateDerivative
  obtain ⟨correctionSmooth, _, _, _, _, _, _, _⟩ :=
    sameGraph_phaseCorrection_exists_uniform_stable_factor graphAnalytic graphZero graphDerivative
      coordinateZero coordinateDerivative
  have nearby : ∀ᶠ point in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 (phaseCorrection 1 graph) point :=
    correctionSmooth.eventually (by norm_num)
  obtain ⟨smoothRadius, smoothPositive, smoothInside⟩ := Metric.mem_nhds_iff.mp nearby
  let radius := min phaseRadius smoothRadius
  refine ⟨radius, by dsimp only [radius]; positivity, (min_le_left _ _).trans phaseSmall, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative
  filter_upwards [phaseFactory scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
    factorPositive factorSmall thresholdSmall referenceNonnegative] with frequency actualPhase
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishNonnegative finishBound small
  have phaseInput (side : Fin 2) (time : ℝ) (member : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| < phaseRadius :=
    (small side time member).trans_le (min_le_left _ _)
  obtain ⟨lift, liftContinuous, initial, polar, phaseJet, literalDerivative, _⟩ :=
    actualPhase prepared path index nonterminal finish finishNonnegative finishBound phaseInput
  refine ⟨lift, liftContinuous, polar, ?_⟩
  have rawSmall (side : Fin 2) (time : ℝ) (member : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| ≤ 1 / 4 :=
    (phaseInput side time member).le.trans phaseSmall
  have smooth (side : Fin 2) (time : ℝ) (member : time ∈ Icc 0 finish) :
      ContDiffAt ℝ 2 (phaseCorrection 1 graph) (unstableShape (cascadePairedMotion prepared side) time index) := by
    apply smoothInside
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans_lt
      ((small side time member).trans_le (min_le_right _ _))
  have geometricDerivative (side : Fin 2) (time : ℝ) (member : time ∈ Icc 0 finish) :
      HasDerivAt (correctedPaperPhase (phaseCorrection 1 graph) (lift side) (cascadePairedMotion prepared side) index)
        (geometricCorrectedPhaseVelocity (phaseCorrection 1 graph) (cascadePairedMotion prepared side) index time) time := by
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith [member.1], by linarith [member.2, finishBound, path.stopBound]⟩
    have localSmooth := (smooth side time member).differentiableAt (by norm_num)
    have localSmall := rawSmall side time member
    have localJet := phaseJet side time member
    fin_cases side
    · exact prepared.trajectory.movingFamily.correctedPaperPhase_hasDerivAt_geometric _ _ index
        (fun _ => globalInside) localSmall localSmooth localJet
    · simp only [cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] at localSmall localSmooth localJet ⊢
      exact prepared.referenceWitness.trajectory.movingFamily.correctedPaperPhase_hasDerivAt_geometric _ _ index
        (fun _ => globalInside) localSmall localSmooth localJet
  have geometricContinuous (side : Fin 2) : ContinuousOn
      (geometricCorrectedPhaseVelocity (phaseCorrection 1 graph) (cascadePairedMotion prepared side) index) (Icc 0 finish) := by
    have globalInside (time : ℝ) (member : time ∈ Icc 0 finish) : time ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith [member.1], by linarith [member.2, finishBound, path.stopBound]⟩
    have localSmooth := smooth side
    have localSmall := rawSmall side
    fin_cases side
    · exact prepared.trajectory.movingFamily.geometricCorrectedPhaseVelocity_continuousOn _ index
        (fun time member _ => globalInside time member) localSmall localSmooth
    · simp only [cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] at localSmall localSmooth ⊢
      exact prepared.referenceWitness.trajectory.movingFamily.geometricCorrectedPhaseVelocity_continuousOn _ index
        (fun time member _ => globalInside time member) localSmall localSmooth
  intro time inside
  have subset : Icc (0 : ℝ) time ⊆ Icc (0 : ℝ) finish := Icc_subset_Icc_right inside.2
  have derivative (current : ℝ) (member : current ∈ Icc 0 time) :=
    (geometricDerivative 0 current (subset member)).sub (geometricDerivative 1 current (subset member))
  have continuous := (geometricContinuous 0).sub (geometricContinuous 1)
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1
    (fun current member => (derivative current member).continuousAt.continuousWithinAt)
    (fun current member => derivative current ⟨member.1.le, member.2.le⟩)
    ((continuous.mono subset).intervalIntegrable_of_Icc inside.1)
  change (∫ current in (0 : ℝ)..time,
    geometricCorrectedPhaseVelocity (phaseCorrection 1 graph) (cascadePairedMotion prepared 0) index current -
      geometricCorrectedPhaseVelocity (phaseCorrection 1 graph) (cascadePairedMotion prepared 1) index current) =
    relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared) index time -
      relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared) index 0 at identity
  rw [initial, sub_zero] at identity
  apply identity.symm.trans
  apply intervalIntegral.integral_congr_ae
  have almostDifferent : ∀ᵐ current : ℝ ∂volume, current ≠ time := by simp [ae_iff]
  filter_upwards [almostDifferent] with current different
  intro member
  rw [uIoc_of_le inside.1] at member
  have closed : current ∈ Icc 0 time := ⟨member.1.le, member.2⟩
  have interior : current ∈ Ioo 0 finish :=
    ⟨member.1, (lt_of_le_of_ne member.2 different).trans_le inside.2⟩
  exact (derivative current closed).unique (literalDerivative current interior)

end EulerNonuniqueness.Paper
