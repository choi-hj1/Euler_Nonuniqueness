import EulerNonuniqueness.Section5.CascadeCorrectedPhaseRate
import EulerNonuniqueness.Section6.DilationFrequencyShear
import EulerNonuniqueness.General.GradedChartInteraction

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem sameGraph_relativeCorrectedPhaseVelocity_exists_shear_bound
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (coordinateZero : coordinate 0 = 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
    ∀ {count : ℕ} (scales : Scales) (motion : Fin 2 → PatchMotion count) (index : Fin count) (time : ℝ),
    (∀ side, |unstableShape (motion side) time index| + |stableShape (motion side) time index| < radius) →
    (∀ side, scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference (motion side) time index) →
    diagonalDifference (motion 1) time index ≤ 2 * scales.length (index.val + 1) ^ 2 →
    ∀ reference : ℝ,
    |(referenceStraightenedShape (motion 1) graph coordinate index time).1| +
      |(referenceStraightenedShape (motion 1) graph coordinate index time).2| ≤ reference →
    let first := referenceStraightenedShape (motion 0) graph coordinate index time
    let second := referenceStraightenedShape (motion 1) graph coordinate index time
    let difference := |first.1 - second.1| + |first.2 - second.2|
    let dilationDifference := (diagonalDifference (motion 0) time index -
      diagonalDifference (motion 1) time index) / scales.length (index.val + 1) ^ 2
    let referenceDefect := |diagonalDifference (motion 1) time index / scales.length (index.val + 1) ^ 2 - 1|
    |relativeCorrectedPaperPhaseVelocity scales (phaseCorrection 1 graph) motion index time -
        scales.omega (index.val + 1) * dilationDifference| ≤
      4 * |scales.omega (index.val + 1)| * |dilationDifference| *
          (2 * |dilationDifference| + 3 * referenceDefect) +
      2 * |scales.omega (index.val + 1)| * constant * ((difference + 2 * reference) * difference) +
      4 * |scales.omega (index.val + 1)| * |dilationDifference| * (constant * reference ^ 2) +
      |correctedPaperPhaseForcing scales (phaseCorrection 1 graph) (motion 0) index time -
        correctedPaperPhaseForcing scales (phaseCorrection 1 graph) (motion 1) index time| := by
  obtain ⟨relativeConstant, relativeNonnegative, relativeRadius, relativePositive, relativeBound⟩ :=
    sameGraph_phaseCorrection_exists_graded_relative_chart_bound graphAnalytic graphZero graphDerivative
      coordinateSmooth coordinateZero coordinateDerivative
  obtain ⟨_, _, _, stableConstant, stableNonnegative, stableRadius, stablePositive, stableBound⟩ :=
    sameGraph_phaseCorrection_exists_uniform_stable_factor graphAnalytic graphZero graphDerivative
      coordinateZero coordinateDerivative
  let constant := max relativeConstant stableConstant
  have constantNonnegative : 0 ≤ constant := relativeNonnegative.trans (le_max_left _ _)
  refine ⟨constant, constantNonnegative, min relativeRadius stableRadius, lt_min relativePositive stablePositive, ?_⟩
  intro count scales motion index time small lower upper reference referenceBound
  dsimp only
  let length := scales.length (index.val + 1)
  let omega := scales.omega (index.val + 1)
  let dilation := fun side => diagonalDifference (motion side) time index / length ^ 2
  let frequency := fun side => omega * length ^ 2 / diagonalDifference (motion side) time index
  let first := referenceStraightenedShape (motion 0) graph coordinate index time
  let second := referenceStraightenedShape (motion 1) graph coordinate index time
  let difference := |first.1 - second.1| + |first.2 - second.2|
  let error := fun side => correctedPhaseError 1 (phaseCorrection 1 graph)
    (unstableShape (motion side) time index, stableShape (motion side) time index)
  have lengthSquaredPositive : 0 < length ^ 2 := sq_pos_of_pos (scales.length_pos _)
  have normalizedLower (side : Fin 2) : (1 / 2 : ℝ) ≤ dilation side := by
    apply (le_div_iff₀ lengthSquaredPositive).mpr
    nlinarith [lower side]
  have normalizedUpper : dilation 1 ≤ 2 := (div_le_iff₀ lengthSquaredPositive).mpr upper
  have frequencyIdentity (side : Fin 2) : frequency side = omega / dilation side := by
    dsimp only [frequency, dilation]
    rw [div_div_eq_mul_div]
  have dilationIdentity : dilation 0 - dilation 1 =
      (diagonalDifference (motion 0) time index - diagonalDifference (motion 1) time index) / length ^ 2 := by
    dsimp only [dilation]
    rw [sub_div]
  have shear := dilation_frequency_shear_remainder_le omega (dilation 0) (dilation 1)
    (normalizedLower 0) (normalizedLower 1) normalizedUpper
  rw [← frequencyIdentity 0, ← frequencyIdentity 1] at shear
  have frequencyBound : |frequency 0| ≤ 2 * |omega| := by
    rw [frequencyIdentity, abs_div, abs_of_pos (by linarith [normalizedLower 0] : 0 < dilation 0)]
    apply (div_le_iff₀ (by linarith [normalizedLower 0] : 0 < dilation 0)).mpr
    nlinarith [mul_le_mul_of_nonneg_left (normalizedLower 0) (abs_nonneg omega)]
  have frequencyDifference := dilation_frequency_difference_le omega (dilation 0) (dilation 1)
    (normalizedLower 0) (normalizedLower 1)
  rw [← frequencyIdentity 0, ← frequencyIdentity 1] at frequencyDifference
  have referenceNonnegative : 0 ≤ reference :=
    (add_nonneg (abs_nonneg second.1) (abs_nonneg second.2)).trans referenceBound
  have stableReference : |second.2| ≤ reference :=
    (le_add_of_nonneg_left (abs_nonneg second.1)).trans referenceBound
  have errorReference : |error 1| ≤ constant * reference ^ 2 := by
    have actual := stableBound 1 _ _ ((small 1).trans_le (min_le_right _ _))
    simp only [abs_one, mul_one] at actual
    change |error 1| ≤ stableConstant * |second.2| * (|second.1| + |second.2|) at actual
    have enlarged := actual.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right relativeConstant stableConstant) (abs_nonneg second.2)) (by positivity))
    have product := mul_le_mul stableReference referenceBound (by positivity : 0 ≤ |second.1| + |second.2|) referenceNonnegative
    have final := mul_le_mul_of_nonneg_left product constantNonnegative
    exact enlarged.trans (by simpa only [mul_assoc, pow_two] using final)
  have errorDifference : |error 0 - error 1| ≤ constant * ((difference + 2 * reference) * difference) := by
    have actual := relativeBound
      (unstableShape (motion 0) time index, stableShape (motion 0) time index)
      (unstableShape (motion 1) time index, stableShape (motion 1) time index)
      ((small 0).trans_le (min_le_left _ _)) ((small 1).trans_le (min_le_left _ _))
    have interaction := EulerNonuniqueness.General.graded_chart_interaction_le first.1 first.2 second.1 second.2 reference referenceBound
    have enlarged := actual.trans (mul_le_mul_of_nonneg_right (le_max_left relativeConstant stableConstant) (by positivity))
    exact enlarged.trans (mul_le_mul_of_nonneg_left interaction constantNonnegative)
  have firstError := mul_le_mul frequencyBound errorDifference (abs_nonneg _) (by positivity : 0 ≤ 2 * |omega|)
  have secondError := mul_le_mul frequencyDifference errorReference (abs_nonneg _) (by positivity : 0 ≤ 4 * |omega| * |dilation 0 - dilation 1|)
  let forcing := correctedPaperPhaseForcing scales (phaseCorrection 1 graph) (motion 0) index time -
    correctedPaperPhaseForcing scales (phaseCorrection 1 graph) (motion 1) index time
  have identity : relativeCorrectedPaperPhaseVelocity scales (phaseCorrection 1 graph) motion index time -
      omega * (dilation 0 - dilation 1) =
    (-(frequency 0 - frequency 1) - omega * (dilation 0 - dilation 1)) +
      frequency 0 * (error 0 - error 1) + (frequency 0 - frequency 1) * error 1 + forcing := by
    dsimp only [relativeCorrectedPaperPhaseVelocity, frequency, error, forcing, omega, length]
    ring
  have triangle := (abs_add
    ((-(frequency 0 - frequency 1) - omega * (dilation 0 - dilation 1)) + frequency 0 * (error 0 - error 1) +
      (frequency 0 - frequency 1) * error 1) forcing).trans
    (add_le_add_right ((abs_add
      ((-(frequency 0 - frequency 1) - omega * (dilation 0 - dilation 1)) + frequency 0 * (error 0 - error 1))
      ((frequency 0 - frequency 1) * error 1)).trans
      (add_le_add_right (abs_add (-(frequency 0 - frequency 1) - omega * (dilation 0 - dilation 1))
        (frequency 0 * (error 0 - error 1))) _)) _)
  rw [← identity] at triangle
  simp only [abs_mul] at triangle
  have bound := triangle.trans (add_le_add_right (add_le_add (add_le_add shear firstError) secondError) _)
  rw [dilationIdentity] at bound
  simpa only [omega, length, dilation, difference, first, second, forcing, mul_assoc] using bound

end EulerNonuniqueness.Paper
