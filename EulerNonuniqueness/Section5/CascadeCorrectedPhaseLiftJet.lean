import EulerNonuniqueness.Section5.CascadeCorrectedPhaseDynamics

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_sameGraph_corrected_phase_lift_jet
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateZero : coordinate 0 = 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
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
      relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared) index 0 = 0 ∧
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift side time : ℂ))) ∧
      (∀ side, ∀ time ∈ Icc 0 finish, HasDerivAt (lift side)
        (deriv (fun current => positiveHalfDiagonal (cascadePairedMotion prepared side) current index) time /
          positiveHalfDiagonal (cascadePairedMotion prepared side) time index).im time) ∧
      (∀ time ∈ Ioo 0 finish,
        HasDerivAt (relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared) index)
          (relativeCorrectedPaperPhaseVelocity {scales with frequency := frequency} (phaseCorrection 1 graph)
            (cascadePairedMotion prepared) index time) time) ∧
      ∀ side, ∀ time ∈ Icc 0 finish,
        |correctedPhaseError 1 (phaseCorrection 1 graph)
          (unstableShape (cascadePairedMotion prepared side) time index,
            stableShape (cascadePairedMotion prepared side) time index)| ≤
          bound * |stableShape (cascadePairedMotion prepared side) time index -
            graph (unstableShape (cascadePairedMotion prepared side) time index)| *
            (|coordinate (unstableShape (cascadePairedMotion prepared side) time index)| +
              |stableShape (cascadePairedMotion prepared side) time index -
                graph (unstableShape (cascadePairedMotion prepared side) time index)|) := by
  obtain ⟨correctionSmooth, correctionZero, correctionDerivative, bound, boundNonnegative,
    phaseRadius, phasePositive, phaseBound⟩ :=
    sameGraph_phaseCorrection_exists_uniform_stable_factor graphAnalytic graphZero graphDerivative coordinateZero coordinateDerivative
  have nearby : ∀ᶠ point in 𝓝 (0 : ℝ), DifferentiableAt ℝ (phaseCorrection 1 graph) point :=
    ((correctionSmooth.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)).eventually (by norm_num)).mono
      (fun _ smooth => smooth.differentiableAt (by norm_num))
  obtain ⟨derivativeRadius, derivativePositive, derivativeInside⟩ := Metric.mem_nhds_iff.mp nearby
  let radius := min phaseRadius (min derivativeRadius (1 / 4))
  refine ⟨bound, boundNonnegative, radius, by dsimp [radius]; positivity,
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_cascade_paired_saddle_admissible amplitudePositive ratioBound alphaPositive rootPositive
      boundaryNonnegative factorPositive (by linarith : factor ≤ 1) thresholdSmall referenceNonnegative,
    scales.eventually_material_prehit_phase_lift amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative]
    with frequency frequencyPositive admissible actualPhase
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishNonnegative finishBound small
  let changed : Scales := {scales with frequency := frequency}
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have rawSmall (side : Fin 2) (time : ℝ) (member : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| ≤ 1 / 4 :=
    (small side time member).le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have radial : ∀ time ∈ Icc 0 finish,
      |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2 := by
    intro time member
    have identity : radialShape prepared.trajectory.movingFamily.patchMotion time index =
        unstableShape prepared.trajectory.movingFamily.patchMotion time index + stableShape prepared.trajectory.movingFamily.patchMotion time index := by
      unfold unstableShape stableShape
      ring
    rw [identity]
    exact (abs_add_le _ _).trans ((rawSmall 0 time member).trans (by norm_num))
  obtain ⟨alternativeLift, alternativeContinuous, alternativeInitial, alternativeProperties⟩ :=
    actualPhase prepared path (thresholdSmall.trans (by norm_num)) factorSmall index nonterminal finish finishNonnegative finishBound radial
  have referenceInside (time : ℝ) (member : time ∈ Icc 0 finish) : time ∈ Icc (0 : ℝ) 2 :=
    ⟨member.1, by linarith [member.2, path.stopBound]⟩
  obtain ⟨referenceLift, referenceContinuous, referenceInitial, referenceProperties⟩ :=
    prepared.referenceWitness.trajectory.movingFamily.exists_reference_phase_on_prefix prepared.referenceWitness.evolution
      (by norm_num : (0 : ℝ) < 2) finishNonnegative amplitudePositive frequencyPositive ratioPositive prepared.referenceWitness.initial
      (by intro time member source; change time ∈ Ioo (-(1 : ℝ)) 3; exact ⟨by linarith [member.1], by linarith [member.2, path.stopBound]⟩)
      (by
        intro time member source
        have lower := (prepared.referenceWitness.coarse.2.1 time (referenceInside time member) source).2.2.1
        have squarePositive := sq_pos_of_pos (changed.length_pos (source.val + 1))
        have scaled := (le_div_iff₀ squarePositive).mp lower
        linarith)
      index
  let lift : Fin 2 → ℝ → ℝ := Fin.cases alternativeLift (fun _ => referenceLift)
  have liftProperties (side : Fin 2) (time : ℝ) (member : time ∈ Icc 0 finish) :
      HasDerivAt (lift side)
        (deriv (fun current => positiveHalfDiagonal (cascadePairedMotion prepared side) current index) time /
          positiveHalfDiagonal (cascadePairedMotion prepared side) time index).im time ∧
      positiveHalfDiagonal (cascadePairedMotion prepared side) time index =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared side) time index‖ : ℂ) *
          Complex.exp (Complex.I * (lift side time : ℂ)) := by
    have rateIdentity (motion : PatchMotion count) :
        -changed.omega (index.val + 1) / referenceDilation changed motion index time + referencePhaseError changed motion index time =
          (deriv (fun current => positiveHalfDiagonal motion current index) time / positiveHalfDiagonal motion time index).im := by
      unfold referencePhaseError
      ring
    fin_cases side
    · have properties := alternativeProperties time member
      rw [rateIdentity] at properties
      exact properties
    · have properties := referenceProperties time member
      rw [rateIdentity] at properties
      simpa only [lift, cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] using properties
  refine ⟨lift, ?_, ?_, fun side time member => (liftProperties side time member).2,
    fun side time member => (liftProperties side time member).1, ?_, ?_⟩
  · intro side
    fin_cases side
    · exact ⟨alternativeContinuous, alternativeInitial⟩
    · exact ⟨referenceContinuous, referenceInitial⟩
  · change correctedPaperPhase (phaseCorrection 1 graph) alternativeLift prepared.trajectory.movingFamily.patchMotion index 0 -
      correctedPaperPhase (phaseCorrection 1 graph) referenceLift prepared.reference index 0 = 0
    simp only [correctedPaperPhase, alternativeInitial, referenceInitial]
    simp only [unstableShape, stableShape, radialShape, angularShape, positiveHalfDiagonal, negativeHalfDiagonal,
      prepared.nonterminal_initial_centroid index nonterminal, sub_self]
  · intro time member
    have actual := admissible prepared path
    have corrected (side : Fin 2) := (actual.1 side).correctedPaperPhase_hasDerivAt path.stopPositive amplitudePositive
      frequencyPositive ratioPositive actual.2.1 (actual.2.2.1 side) (actual.2.2.2 side) index
      ⟨member.1, member.2.trans_le finishBound⟩ (rawSmall side time ⟨member.1.le, member.2.le⟩)
      (liftProperties side time ⟨member.1.le, member.2.le⟩).1
      (derivativeInside (show unstableShape (cascadePairedMotion prepared side) time index ∈ Metric.ball (0 : ℝ) derivativeRadius by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
        exact (le_add_of_nonneg_right (abs_nonneg _)).trans_lt
          ((small side time ⟨member.1.le, member.2.le⟩).trans_le ((min_le_right _ _).trans (min_le_left _ _)))))
    have derivative := (corrected 0).sub (corrected 1)
    convert derivative using 1
    dsimp only [relativeCorrectedPaperPhaseVelocity]
    ring
  · intro side time member
    have actual := phaseBound 1 (unstableShape (cascadePairedMotion prepared side) time index)
      (stableShape (cascadePairedMotion prepared side) time index) ((small side time member).trans_le (min_le_left _ _))
    simpa only [abs_one, mul_one] using actual

end EulerNonuniqueness.Paper

