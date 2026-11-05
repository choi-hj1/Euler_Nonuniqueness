import EulerNonuniqueness.Section6.PhaseCorrectionRelativeFiber
import EulerNonuniqueness.Section6.NormalFormInverseMatching

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem sameGraph_phaseCorrection_exists_graded_relative_chart_bound
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (coordinateZero : coordinate 0 = 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ first second : ℝ × ℝ,
      |first.1| + |first.2| < radius → |second.1| + |second.2| < radius →
      let firstChart := localNormalFormChart graph coordinate first
      let secondChart := localNormalFormChart graph coordinate second
      |correctedPhaseError 1 (phaseCorrection 1 graph) first - correctedPhaseError 1 (phaseCorrection 1 graph) second| ≤
        constant * ((|firstChart.2| + |secondChart.2|) * |firstChart.1 - secondChart.1| +
          (|firstChart.1| + |secondChart.1| + |firstChart.2| + |secondChart.2|) * |firstChart.2 - secondChart.2|) := by
  obtain ⟨fiberConstant, fiberNonnegative, fiberRadius, fiberPositive, relative⟩ :=
    sameGraph_phaseCorrection_exists_graded_relative_fiber_bound graphAnalytic graphZero graphDerivative
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverseBound⟩ :=
    localNormalFormChart_exists_uniform_inverse_lipschitz (graphAnalytic.contDiffAt (n := 2)) coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  have sizeContinuous : ContinuousAt (fun point : ℝ × ℝ => |point.1| + |point.2 - graph point.1|) 0 :=
    continuous_fst.continuousAt.abs.add (continuous_snd.continuousAt.sub
      (graphAnalytic.continuousAt.comp (f := fun point : ℝ × ℝ => point.1) continuous_fst.continuousAt)).abs
  have smallFiber := sizeContinuous.eventually (eventually_lt_nhds
    (by simpa only [Prod.fst_zero, Prod.snd_zero, graphZero, sub_zero, abs_zero, zero_add] using fiberPositive))
  obtain ⟨rawRadius, rawPositive, rawInside⟩ := Metric.mem_nhds_iff.mp smallFiber
  let radius := min inverseRadius rawRadius
  have radiusPositive : 0 < radius := lt_min inversePositive rawPositive
  have chartZero : localNormalFormChart graph coordinate (0 : ℝ × ℝ) = 0 := by
    simp only [localNormalFormChart, Prod.fst_zero, Prod.snd_zero, graphZero, coordinateZero, sub_zero, Prod.mk_zero_zero]
  have comparison (first second : ℝ × ℝ) (firstSmall : |first.1| + |first.2| < radius)
      (secondSmall : |second.1| + |second.2| < radius) :
      |first.1 - second.1| ≤ inverseConstant *
        (|(localNormalFormChart graph coordinate first).1 - (localNormalFormChart graph coordinate second).1| +
          |(localNormalFormChart graph coordinate first).2 - (localNormalFormChart graph coordinate second).2|) := by
    have inverse := inverseBound first second (firstSmall.trans_le (min_le_left _ _))
      (secondSmall.trans_le (min_le_left _ _))
    apply (le_add_of_nonneg_right (abs_nonneg (first.2 - second.2))).trans inverse |>.trans
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  have fiberSmall (point : ℝ × ℝ) (small : |point.1| + |point.2| < radius) :
      |point.1| + |point.2 - graph point.1| < fiberRadius := by
    apply rawInside
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (max_le (le_add_of_nonneg_right (abs_nonneg _))
      (le_add_of_nonneg_left (abs_nonneg _))).trans_lt (small.trans_le (min_le_right _ _))
  refine ⟨fiberConstant * (2 * inverseConstant + 1), by positivity, radius, radiusPositive, ?_⟩
  intro first second firstSmall secondSmall
  dsimp only
  let firstChart := localNormalFormChart graph coordinate first
  let secondChart := localNormalFormChart graph coordinate second
  have raw := relative (first.1, first.2 - graph first.1) (second.1, second.2 - graph second.1)
    (fiberSmall first firstSmall) (fiberSmall second secondSmall)
  have reconstruct (point : ℝ × ℝ) : (point.1, graph point.1 + (point.2 - graph point.1)) = point := by
    ext <;> simp
  rw [reconstruct first, reconstruct second] at raw
  have unstableDifference := comparison first second firstSmall secondSmall
  have firstSize := comparison first 0 firstSmall (by simpa using radiusPositive)
  have secondSize := comparison second 0 secondSmall (by simpa using radiusPositive)
  rw [chartZero] at firstSize secondSize
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at firstSize secondSize
  have firstTerm := mul_le_mul_of_nonneg_left unstableDifference
    (add_nonneg (abs_nonneg firstChart.2) (abs_nonneg secondChart.2))
  have secondTerm := mul_le_mul_of_nonneg_right
    (add_le_add_right (add_le_add firstSize secondSize) (|firstChart.2| + |secondChart.2|))
    (abs_nonneg (firstChart.2 - secondChart.2))
  have extra : 0 ≤ (inverseConstant + 1) *
      ((|firstChart.2| + |secondChart.2|) * |firstChart.1 - secondChart.1| +
        (|firstChart.1| + |secondChart.1|) * |firstChart.2 - secondChart.2|) := by positivity
  have scalarBound : (|firstChart.2| + |secondChart.2|) * |first.1 - second.1| +
      (|first.1| + |second.1| + |firstChart.2| + |secondChart.2|) * |firstChart.2 - secondChart.2| ≤
      (2 * inverseConstant + 1) *
        ((|firstChart.2| + |secondChart.2|) * |firstChart.1 - secondChart.1| +
          (|firstChart.1| + |secondChart.1| + |firstChart.2| + |secondChart.2|) * |firstChart.2 - secondChart.2|) := by
    change (|firstChart.2| + |secondChart.2|) * |first.1 - second.1| ≤ _ at firstTerm
    change (|first.1| + |second.1| + (|firstChart.2| + |secondChart.2|)) * |firstChart.2 - secondChart.2| ≤ _ at secondTerm
    nlinarith only [firstTerm, secondTerm, extra]
  apply raw.trans
  simpa only [firstChart, secondChart, localNormalFormChart, mul_assoc] using
    mul_le_mul_of_nonneg_left scalarBound fiberNonnegative

end EulerNonuniqueness.Section6
