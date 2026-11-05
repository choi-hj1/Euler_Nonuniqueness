import EulerNonuniqueness.Section5.CascadeCorrectedPhaseDynamics
import EulerNonuniqueness.Section6.PhaseCorrectionRelativeCoordinates
import EulerNonuniqueness.Section6.DiagonalFrequencyDifference

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem sameGraph_relativeCorrectedPhaseVelocity_exists_graded_bound
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (coordinateZero : coordinate 0 = 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
    ∀ {count : ℕ} (scales : Scales) (motion : Fin 2 → PatchMotion count) (index : Fin count) (time : ℝ),
    (∀ side, |unstableShape (motion side) time index| + |stableShape (motion side) time index| < radius) →
    (∀ side, scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference (motion side) time index) →
    let first := referenceStraightenedShape (motion 0) graph coordinate index time
    let second := referenceStraightenedShape (motion 1) graph coordinate index time
    let dilationDifference := |diagonalDifference (motion 0) time index -
      diagonalDifference (motion 1) time index| / scales.length (index.val + 1) ^ 2
    |relativeCorrectedPaperPhaseVelocity scales (phaseCorrection 1 graph) motion index time| ≤
      4 * |scales.omega (index.val + 1)| * dilationDifference *
        (1 + constant * |second.2| * (|second.1| + |second.2|)) +
      2 * |scales.omega (index.val + 1)| * constant *
        ((|first.2| + |second.2|) * |first.1 - second.1| +
          (|first.1| + |second.1| + |first.2| + |second.2|) * |first.2 - second.2|) +
      |correctedPaperPhaseForcing scales (phaseCorrection 1 graph) (motion 0) index time -
        correctedPaperPhaseForcing scales (phaseCorrection 1 graph) (motion 1) index time| := by
  obtain ⟨relativeConstant, relativeNonnegative, relativeRadius, relativePositive, relativeBound⟩ :=
    sameGraph_phaseCorrection_exists_graded_relative_chart_bound graphAnalytic graphZero graphDerivative
      coordinateSmooth coordinateZero coordinateDerivative
  obtain ⟨_, _, _, stableConstant, stableNonnegative, stableRadius, stablePositive, stableBound⟩ :=
    sameGraph_phaseCorrection_exists_uniform_stable_factor graphAnalytic graphZero graphDerivative
      coordinateZero coordinateDerivative
  let constant := max relativeConstant stableConstant
  refine ⟨constant, relativeNonnegative.trans (le_max_left _ _), min relativeRadius stableRadius,
    lt_min relativePositive stablePositive, ?_⟩
  intro count scales motion index time small lower
  let frequency := fun side => scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 /
    diagonalDifference (motion side) time index
  let first := referenceStraightenedShape (motion 0) graph coordinate index time
  let second := referenceStraightenedShape (motion 1) graph coordinate index time
  let difference := |diagonalDifference (motion 0) time index - diagonalDifference (motion 1) time index| /
    scales.length (index.val + 1) ^ 2
  let graded := (|first.2| + |second.2|) * |first.1 - second.1| +
    (|first.1| + |second.1| + |first.2| + |second.2|) * |first.2 - second.2|
  have frequencyDifference : |frequency 0 - frequency 1| ≤
      4 * |scales.omega (index.val + 1)| * difference :=
    diagonal_frequency_difference_le scales (motion 0) (motion 1) index time (lower 0) (lower 1)
  have frequencyBound : |frequency 0| ≤ 2 * |scales.omega (index.val + 1)| := by
    have squarePositive := sq_pos_of_pos (scales.length_pos (index.val + 1))
    have denominatorPositive : 0 < diagonalDifference (motion 0) time index := by
      exact (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le (lower 0)
    dsimp only [frequency]
    rw [abs_div, abs_mul, abs_of_pos squarePositive, abs_of_pos denominatorPositive]
    apply (div_le_iff₀ denominatorPositive).mpr
    nlinarith [mul_le_mul_of_nonneg_left (lower 0) (abs_nonneg (scales.omega (index.val + 1)))]
  have errorDifference :
      |correctedPhaseError 1 (phaseCorrection 1 graph)
          (unstableShape (motion 0) time index, stableShape (motion 0) time index) -
        correctedPhaseError 1 (phaseCorrection 1 graph)
          (unstableShape (motion 1) time index, stableShape (motion 1) time index)| ≤ constant * graded := by
    apply (relativeBound _ _ ((small 0).trans_le (min_le_left _ _))
      ((small 1).trans_le (min_le_left _ _))).trans
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have referenceError : |correctedPhaseError 1 (phaseCorrection 1 graph)
      (unstableShape (motion 1) time index, stableShape (motion 1) time index)| ≤
      constant * |second.2| * (|second.1| + |second.2|) := by
    have actual := stableBound 1 _ _ ((small 1).trans_le (min_le_right _ _))
    simp only [abs_one, mul_one] at actual
    change |correctedPhaseError 1 (phaseCorrection 1 graph)
      (unstableShape (motion 1) time index, stableShape (motion 1) time index)| ≤
      constant * |stableShape (motion 1) time index - graph (unstableShape (motion 1) time index)| *
        (|coordinate (unstableShape (motion 1) time index)| +
          |stableShape (motion 1) time index - graph (unstableShape (motion 1) time index)|)
    exact actual.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)) (by positivity))
  have firstTerm := mul_le_mul frequencyBound errorDifference (abs_nonneg _)
    (by positivity : 0 ≤ 2 * |scales.omega (index.val + 1)|)
  have secondTerm := mul_le_mul frequencyDifference referenceError (abs_nonneg _)
    (by dsimp [difference]; positivity : 0 ≤ 4 * |scales.omega (index.val + 1)| * difference)
  have triangle := abs_add (-(frequency 0 - frequency 1) +
      frequency 0 * (correctedPhaseError 1 (phaseCorrection 1 graph)
        (unstableShape (motion 0) time index, stableShape (motion 0) time index) -
        correctedPhaseError 1 (phaseCorrection 1 graph)
        (unstableShape (motion 1) time index, stableShape (motion 1) time index)))
    ((frequency 0 - frequency 1) * correctedPhaseError 1 (phaseCorrection 1 graph)
      (unstableShape (motion 1) time index, stableShape (motion 1) time index))
  have firstTriangle := abs_add (-(frequency 0 - frequency 1))
    (frequency 0 * (correctedPhaseError 1 (phaseCorrection 1 graph)
      (unstableShape (motion 0) time index, stableShape (motion 0) time index) -
      correctedPhaseError 1 (phaseCorrection 1 graph)
      (unstableShape (motion 1) time index, stableShape (motion 1) time index)))
  simp only [abs_neg, abs_mul] at triangle firstTriangle
  dsimp only [relativeCorrectedPaperPhaseVelocity]
  apply (abs_add _ _).trans
  dsimp only
  have combined := triangle.trans (add_le_add_right firstTriangle _)
  dsimp only [frequency] at combined firstTerm secondTerm frequencyDifference
  dsimp only [first, second, difference, graded] at firstTerm secondTerm frequencyDifference ⊢
  nlinarith

end EulerNonuniqueness.Paper
