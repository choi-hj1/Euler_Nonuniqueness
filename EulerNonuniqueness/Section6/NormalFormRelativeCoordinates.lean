import EulerNonuniqueness.Section6.NormalFormFiberRelative
import EulerNonuniqueness.Section6.PaperStraightenedShapeDynamics

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem exists_uniform_localNormalForm_relative_coordinates :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ frequency : ℝ, ∀ first second : ℝ × ℝ,
      |first.1| + |first.2| < radius → |second.1| + |second.2| < radius →
      let firstChart := localNormalFormChart graph coordinate first
      let secondChart := localNormalFormChart graph coordinate second
      ‖localNormalFormError frequency graph coordinate first - localNormalFormError frequency graph coordinate second‖ ≤
        constant * |frequency| * ((|firstChart.2| + |secondChart.2|) * |firstChart.1 - secondChart.1| +
          (|firstChart.1| + |secondChart.1| + |firstChart.2| + |secondChart.2|) * |firstChart.2 - secondChart.2|) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    fiberConstant, fiberNonnegative, fiberRadius, fiberPositive, relative⟩ := exists_localNormalForm_graded_relative_remainder
  have chartRegular := localNormalFormChart_regular (graphAnalytic.contDiffAt (n := 2)) coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨inverse, inverseSmooth, inverseZero, leftInverse, rightInverse⟩ := localNormalFormChart_local_inverse
    (graphAnalytic.contDiffAt (n := 2)) coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  have inverseOnce : ContDiffAt ℝ 1 inverse 0 := inverseSmooth.of_le (by norm_num)
  obtain ⟨inverseBound, inverseRegion, inverseRegionMem, inverseLipschitz⟩ := inverseOnce.exists_lipschitzOnWith
  have chartTendsto : Tendsto (localNormalFormChart graph coordinate) (nhds (0 : ℝ × ℝ)) (nhds 0) := by
    simpa only [chartRegular.2.1] using chartRegular.1.continuousAt.tendsto
  have imageInside := chartTendsto.eventually inverseRegionMem
  have graphComposition : ContinuousAt (fun point : ℝ × ℝ => graph point.1) 0 :=
    graphAnalytic.continuousAt.comp (f := fun point : ℝ × ℝ => point.1) continuous_fst.continuousAt
  have sizeContinuous : ContinuousAt (fun point : ℝ × ℝ => |point.1| + |point.2 - graph point.1|) 0 :=
    continuous_fst.continuousAt.abs.add ((continuous_snd.continuousAt.sub graphComposition).abs)
  have fiberSmall : ∀ᶠ point in nhds (0 : ℝ × ℝ), |point.1| + |point.2 - graph point.1| < fiberRadius :=
    sizeContinuous.eventually (eventually_lt_nhds (by simpa only [Prod.fst_zero, Prod.snd_zero, graphZero, sub_zero, abs_zero, zero_add] using fiberPositive))
  obtain ⟨radius, radiusPositive, inside⟩ := Metric.mem_nhds_iff.mp (leftInverse.and (imageInside.and fiberSmall))
  let constant := fiberConstant * (2 * (inverseBound : ℝ) + 1)
  have constantNonnegative : 0 ≤ constant := by dsimp only [constant]; positivity
  have pointInside (point : ℝ × ℝ) (small : |point.1| + |point.2| < radius) : point ∈ Metric.ball (0 : ℝ × ℝ) radius := by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (max_le (le_add_of_nonneg_right (abs_nonneg point.2)) (le_add_of_nonneg_left (abs_nonneg point.1))).trans_lt small
  have chartZero : localNormalFormChart graph coordinate (0 : ℝ × ℝ) = 0 := chartRegular.2.1
  have comparison (first second : ℝ × ℝ) (firstSmall : |first.1| + |first.2| < radius)
      (secondSmall : |second.1| + |second.2| < radius) :
      |first.1 - second.1| ≤ (inverseBound : ℝ) *
        (|(localNormalFormChart graph coordinate first).1 - (localNormalFormChart graph coordinate second).1| +
          |(localNormalFormChart graph coordinate first).2 - (localNormalFormChart graph coordinate second).2|) := by
    have firstData := inside (pointInside first firstSmall)
    have secondData := inside (pointInside second secondSmall)
    have actual := (lipschitzOnWith_iff_norm_sub_le.mp inverseLipschitz) firstData.2.1 secondData.2.1
    rw [firstData.1, secondData.1] at actual
    have firstProjection : |first.1 - second.1| ≤ ‖first - second‖ := by simpa only [Prod.fst_sub, Real.norm_eq_abs] using norm_fst_le (first - second)
    apply (firstProjection.trans actual).trans
    apply mul_le_mul_of_nonneg_left _ inverseBound.coe_nonneg
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  have zeroSmall : |(0 : ℝ × ℝ).1| + |(0 : ℝ × ℝ).2| < radius := by simpa only [Prod.fst_zero, Prod.snd_zero, abs_zero, zero_add] using radiusPositive
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    constant, constantNonnegative, radius, radiusPositive, ?_⟩
  intro frequency first second firstSmall secondSmall
  dsimp only
  let firstChart := localNormalFormChart graph coordinate first
  let secondChart := localNormalFormChart graph coordinate second
  have firstData := inside (pointInside first firstSmall)
  have secondData := inside (pointInside second secondSmall)
  have raw := relative (first.1, first.2 - graph first.1) (second.1, second.2 - graph second.1) firstData.2.2 secondData.2.2
  simp only [add_sub_cancel] at raw
  have unstableDifference := comparison first second firstSmall secondSmall
  have firstSize := comparison first 0 firstSmall zeroSmall
  have secondSize := comparison second 0 secondSmall zeroSmall
  rw [chartZero] at firstSize secondSize
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at firstSize secondSize
  have firstTerm := mul_le_mul_of_nonneg_left unstableDifference (add_nonneg (abs_nonneg firstChart.2) (abs_nonneg secondChart.2))
  have secondTerm := mul_le_mul_of_nonneg_right (add_le_add_right (add_le_add firstSize secondSize) (|firstChart.2| + |secondChart.2|))
    (abs_nonneg (firstChart.2 - secondChart.2))
  have extra : 0 ≤ ((inverseBound : ℝ) + 1) *
      ((|firstChart.2| + |secondChart.2|) * |firstChart.1 - secondChart.1| +
        (|firstChart.1| + |secondChart.1|) * |firstChart.2 - secondChart.2|) := by positivity
  have scalarBound : (|firstChart.2| + |secondChart.2|) * |first.1 - second.1| +
      (|first.1| + |second.1| + |firstChart.2| + |secondChart.2|) * |firstChart.2 - secondChart.2| ≤
      (2 * (inverseBound : ℝ) + 1) *
        ((|firstChart.2| + |secondChart.2|) * |firstChart.1 - secondChart.1| +
          (|firstChart.1| + |secondChart.1| + |firstChart.2| + |secondChart.2|) * |firstChart.2 - secondChart.2|) := by
    change (|firstChart.2| + |secondChart.2|) * |first.1 - second.1| ≤ _ at firstTerm
    change (|first.1| + |second.1| + (|firstChart.2| + |secondChart.2|)) * |firstChart.2 - secondChart.2| ≤ _ at secondTerm
    nlinarith only [firstTerm, secondTerm, extra]
  have normalized : ‖localNormalFormError 1 graph coordinate first - localNormalFormError 1 graph coordinate second‖ ≤
      constant * ((|firstChart.2| + |secondChart.2|) * |firstChart.1 - secondChart.1| +
        (|firstChart.1| + |secondChart.1| + |firstChart.2| + |secondChart.2|) * |firstChart.2 - secondChart.2|) := by
    apply raw.trans
    simpa only [firstChart, secondChart, localNormalFormChart, constant, mul_assoc] using mul_le_mul_of_nonneg_left scalarBound fiberNonnegative
  rw [localNormalFormError_frequency_smul frequency graph coordinate first,
    localNormalFormError_frequency_smul frequency graph coordinate second, ← smul_sub, norm_smul, Real.norm_eq_abs]
  have actual := mul_le_mul_of_nonneg_left normalized (abs_nonneg frequency)
  simpa only [firstChart, secondChart, mul_assoc, mul_comm, mul_left_comm] using actual

end EulerNonuniqueness.Section6
