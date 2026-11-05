import EulerNonuniqueness.Section5.CascadeFiniteCoordinateGeometry
import EulerNonuniqueness.General.ComplexPhaseUniqueness

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.eventually_cascade_phase_lift_coherence (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {referenceConstant : ℝ} (referenceNonnegative : 0 ≤ referenceConstant) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {cap : ℝ} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeSourcePreparedPair cap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 4) →
    ∀ firstLift secondLift : Fin 2 → ℝ → ℝ,
    (∀ side, ContinuousOn (firstLift side) (Icc 0 finish)) →
    (∀ side, ContinuousOn (secondLift side) (Icc 0 finish)) →
    (∀ side, firstLift side 0 = secondLift side 0) →
    (∀ side, ∀ time ∈ Icc 0 finish,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
          Complex.exp (Complex.I * (firstLift side time : ℂ))) →
    (∀ side, ∀ time ∈ Icc 0 finish,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
          Complex.exp (Complex.I * (secondLift side time : ℂ))) →
    (∀ side, EqOn (firstLift side) (secondLift side) (Icc 0 finish)) ∧
    (∀ correction : ℝ → ℝ,
      EqOn (relativeCorrectedPaperPhase correction firstLift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index)
        (relativeCorrectedPaperPhase correction secondLift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index) (Icc 0 finish)) ∧
    ∀ graph coordinate : ℝ → ℝ,
      EqOn (prepared.finiteCoordinateSize graph coordinate firstLift index)
        (prepared.finiteCoordinateSize graph coordinate secondLift index) (Icc 0 finish) := by
  filter_upwards [scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative
    (by norm_num : (0 : ℝ) < 1 / 4)] with frequency referenceSmall
  intro cap orbit sectionTime phase dipoleAngle threshold scaleRoot shapeRadius factor monitor boundaryConstant count
    prepared path index finish finishNonnegative finishBound chartSmall firstLift secondLift
    firstContinuous secondContinuous initial firstPolar secondPolar
  have pairedSmall (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| +
        |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| ≤ 1 / 4 := by
    fin_cases side
    · exact chartSmall time inside
    · have actual := referenceSmall prepared.toCascadeMaterialPreparedPair time
        ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩ index
      change |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| ≤ 1 / 4
      have diagonalNonnegative := abs_nonneg (diagonalDifference prepared.reference time index /
        ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 - 1)
      linarith only [actual, diagonalNonnegative]
  have nonzero (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index ≠ 0 := by
    have upper := paper_shape_ratio_im_pos_of_small
      (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index (pairedSmall side time inside)
    intro zero
    simp only [zero, div_zero, Complex.zero_im, lt_self_iff_false] at upper
  have liftEquality (side : Fin 2) : EqOn (firstLift side) (secondLift side) (Icc 0 finish) :=
    General.phase_polar_lift_unique_on_Icc finishNonnegative (firstContinuous side) (secondContinuous side)
      (initial side) (nonzero side) (firstPolar side) (secondPolar side)
  have correctedEquality (correction : ℝ → ℝ) :
      EqOn (relativeCorrectedPaperPhase correction firstLift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index)
        (relativeCorrectedPaperPhase correction secondLift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index) (Icc 0 finish) := by
    intro time inside
    dsimp only [relativeCorrectedPaperPhase, correctedPaperPhase]
    rw [liftEquality 0 inside, liftEquality 1 inside]
  refine ⟨liftEquality, correctedEquality, ?_⟩
  intro graph coordinate time inside
  dsimp only [CascadeSourcePreparedPair.finiteCoordinateSize]
  rw [correctedEquality (phaseCorrection 1 graph) inside]

end EulerNonuniqueness.Paper
