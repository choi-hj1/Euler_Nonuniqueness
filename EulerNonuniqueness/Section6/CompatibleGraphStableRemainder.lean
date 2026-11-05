import EulerNonuniqueness.Section6.CompatibleAnalyticGraphInvariant
import EulerNonuniqueness.Section6.NormalFormChartComparison

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem compatible_graph_paired_stable_remainder_bound
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (compatible : ∀ᶠ time : ℝ in atBot,
      orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ), ∀ first second : ℝ × ℝ,
      |first.1| + |first.2| < radius → |second.1| + |second.2| < radius →
      let firstChart := localNormalFormChart graph coordinate first
      let secondChart := localNormalFormChart graph coordinate second
      let shape := |firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|
      let reference := |secondChart.1| + |secondChart.2|
      |(localNormalFormError 1 graph coordinate first).2 -
          (localNormalFormError 1 graph coordinate second).2| ≤
        constant * ((shape + reference) * |firstChart.2 - secondChart.2| + reference * shape) := by
  obtain ⟨comparisonGraph, comparisonCoordinate, comparisonAnalytic, comparisonZero,
    comparisonDerivative, comparisonSmooth, comparisonCoordinateZero, comparisonCoordinateDerivative,
    fiberConstant, fiberNonnegative, fiberRadius, fiberPositive, relative⟩ :=
    exists_uniform_localNormalForm_relative_coordinates
  have graded := fun first second firstSmall secondSmall => by
    simpa only [abs_one, mul_one] using relative 1 first second firstSmall secondSmall
  have stableBound := localNormalForm_stable_bound_of_graded comparisonZero comparisonCoordinateZero
    fiberNonnegative fiberPositive graded
  have comparisonCompatible := normalizedSeparatingOrbit_on_normalForm_graph
    (comparisonAnalytic.contDiffAt (n := 1)) comparisonSmooth.continuousAt comparisonZero
    comparisonCoordinateZero fiberPositive stableBound orbit normalized
  have unstableLimit : Tendsto (orbitUnstableShape orbit) atBot (𝓝 0) :=
    continuous_fst.continuousAt.tendsto.comp (normalizedSeparatingOrbit_shape_tendsto_zero orbit normalized)
  have punctured : Tendsto (orbitUnstableShape orbit) atBot (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨unstableLimit,
      (normalizedSeparatingOrbit_eventually_positive_unstable orbit normalized).mono
        (fun _ positive => ne_of_gt positive)⟩
  have graphEquality : graph =ᶠ[𝓝 (0 : ℝ)] comparisonGraph :=
    General.analytic_germ_eq_of_eq_along_punctured_curve graphAnalytic comparisonAnalytic punctured (by
      filter_upwards [compatible, comparisonCompatible] with time first second
      exact first.symm.trans second)
  obtain ⟨germRadius, germPositive, germInside⟩ := Metric.mem_nhds_iff.mp
    (graphEquality.and graphEquality.deriv)
  obtain ⟨comparisonRadius, comparisonPositive, comparisonConstant, comparisonOne, comparison⟩ :=
    localNormalFormChart_exists_uniform_comparison graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative comparisonAnalytic comparisonSmooth comparisonZero
      comparisonCoordinateZero comparisonDerivative comparisonCoordinateDerivative
  let radius := min germRadius (min fiberRadius comparisonRadius)
  let constant := 4 * fiberConstant * (comparisonConstant + 1) + 1
  have comparisonNonnegative : 0 ≤ comparisonConstant := zero_le_one.trans comparisonOne
  have constantBound : 4 * fiberConstant * (comparisonConstant + 1) ≤ constant := by
    dsimp only [constant]
    linarith
  refine ⟨radius, lt_min germPositive (lt_min fiberPositive comparisonPositive),
    constant, by
      have product : 0 ≤ 4 * fiberConstant * (comparisonConstant + 1) := by positivity
      dsimp only [constant]
      linarith only [product], ?_⟩
  intro first second firstSmall secondSmall
  have pointGerm (point : ℝ × ℝ) (small : |point.1| + |point.2| < radius) :
      graph point.1 = comparisonGraph point.1 ∧ deriv graph point.1 = deriv comparisonGraph point.1 := by
    apply germInside
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact (le_add_of_nonneg_right (abs_nonneg point.2)).trans_lt
      (small.trans_le (min_le_left _ _))
  have errorIdentity (point : ℝ × ℝ) (small : |point.1| + |point.2| < radius) :
      (localNormalFormError 1 graph coordinate point).2 =
        (localNormalFormError 1 comparisonGraph comparisonCoordinate point).2 := by
    simp only [localNormalFormError, (pointGerm point small).1, (pointGerm point small).2]
  have stableIdentity (point : ℝ × ℝ) (small : |point.1| + |point.2| < radius) :
      (localNormalFormChart comparisonGraph comparisonCoordinate point).2 =
        (localNormalFormChart graph coordinate point).2 := by
    simp only [localNormalFormChart, (pointGerm point small).1]
  have forward (left right : ℝ × ℝ) (leftSmall : |left.1| + |left.2| < radius)
      (rightSmall : |right.1| + |right.2| < radius) :
      |(localNormalFormChart comparisonGraph comparisonCoordinate left).1 -
        (localNormalFormChart comparisonGraph comparisonCoordinate right).1| ≤
        comparisonConstant *
          (|(localNormalFormChart graph coordinate left).1 - (localNormalFormChart graph coordinate right).1| +
            |(localNormalFormChart graph coordinate left).2 - (localNormalFormChart graph coordinate right).2|) := by
    have bound := comparison left right
      (leftSmall.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
      (rightSmall.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans
      ((le_add_of_nonneg_right (abs_nonneg _)).trans bound)
  let firstChart := localNormalFormChart graph coordinate first
  let secondChart := localNormalFormChart graph coordinate second
  let shape := |firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|
  let reference := |secondChart.1| + |secondChart.2|
  let stable := |firstChart.2 - secondChart.2|
  have shapeNonnegative : 0 ≤ shape := by dsimp only [shape]; positivity
  have referenceNonnegative : 0 ≤ reference := by dsimp only [reference]; positivity
  have stableNonnegative : 0 ≤ stable := abs_nonneg _
  have stableBelow : stable ≤ shape := le_add_of_nonneg_left (abs_nonneg _)
  have zeroSmall : |(0 : ℝ × ℝ).1| + |(0 : ℝ × ℝ).2| < radius := by
    simpa only [Prod.fst_zero, Prod.snd_zero, abs_zero, zero_add] using
      (lt_min germPositive (lt_min fiberPositive comparisonPositive))
  have chartZero : localNormalFormChart graph coordinate 0 = 0 := by
    simp only [localNormalFormChart, Prod.fst_zero, Prod.snd_zero, coordinateZero, graphZero, sub_zero, Prod.mk_zero_zero]
  have comparisonChartZero : localNormalFormChart comparisonGraph comparisonCoordinate 0 = 0 := by
    simp only [localNormalFormChart, Prod.fst_zero, Prod.snd_zero, comparisonCoordinateZero, comparisonZero, sub_zero, Prod.mk_zero_zero]
  have firstSize : |firstChart.1| + |firstChart.2| ≤ shape + reference := by
    have firstBound := abs_sub_abs_le_abs_sub firstChart.1 secondChart.1
    have secondBound := abs_sub_abs_le_abs_sub firstChart.2 secondChart.2
    dsimp only [shape, reference]
    linarith only [firstBound, secondBound]
  have unstableDifference := forward first second firstSmall secondSmall
  change _ ≤ comparisonConstant * shape at unstableDifference
  have firstUnstable := forward first 0 firstSmall zeroSmall
  rw [chartZero, comparisonChartZero] at firstUnstable
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at firstUnstable
  have firstUnstableBound : |(localNormalFormChart comparisonGraph comparisonCoordinate first).1| ≤
      comparisonConstant * (shape + reference) :=
    firstUnstable.trans (mul_le_mul_of_nonneg_left firstSize comparisonNonnegative)
  have secondUnstable := forward second 0 secondSmall zeroSmall
  rw [chartZero, comparisonChartZero] at secondUnstable
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at secondUnstable
  change _ ≤ comparisonConstant * reference at secondUnstable
  have stableSum : |firstChart.2| + |secondChart.2| ≤ stable + 2 * reference := by
    have bound := abs_sub_abs_le_abs_sub firstChart.2 secondChart.2
    have secondBelow : |secondChart.2| ≤ reference := le_add_of_nonneg_left (abs_nonneg _)
    dsimp only [stable]
    linarith only [bound, secondBelow]
  have raw := graded first second
    (firstSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    (secondSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have component := (norm_snd_le (localNormalFormError 1 comparisonGraph comparisonCoordinate first -
    localNormalFormError 1 comparisonGraph comparisonCoordinate second)).trans raw
  simp only [Prod.snd_sub, Real.norm_eq_abs, stableIdentity first firstSmall, stableIdentity second secondSmall] at component
  change _ ≤ fiberConstant * ((|firstChart.2| + |secondChart.2|) *
    |(localNormalFormChart comparisonGraph comparisonCoordinate first).1 -
      (localNormalFormChart comparisonGraph comparisonCoordinate second).1| +
    (|(localNormalFormChart comparisonGraph comparisonCoordinate first).1| +
      |(localNormalFormChart comparisonGraph comparisonCoordinate second).1| + |firstChart.2| + |secondChart.2|) * stable) at component
  have enlarged : |(localNormalFormError 1 comparisonGraph comparisonCoordinate first).2 -
      (localNormalFormError 1 comparisonGraph comparisonCoordinate second).2| ≤
      fiberConstant * ((stable + 2 * reference) * (comparisonConstant * shape) +
      (comparisonConstant * (shape + reference) + comparisonConstant * reference +
        (stable + 2 * reference)) * stable) := by
    apply component.trans
    have totalSize : |(localNormalFormChart comparisonGraph comparisonCoordinate first).1| +
        |(localNormalFormChart comparisonGraph comparisonCoordinate second).1| +
        |firstChart.2| + |secondChart.2| ≤
        comparisonConstant * (shape + reference) + comparisonConstant * reference +
          (stable + 2 * reference) := by
      linarith only [firstUnstableBound, secondUnstable, stableSum]
    apply mul_le_mul_of_nonneg_left _ fiberNonnegative
    exact add_le_add
      (mul_le_mul stableSum unstableDifference (abs_nonneg _) (by positivity))
      (mul_le_mul_of_nonneg_right totalSize stableNonnegative)
  have scalar : (stable + 2 * reference) * (comparisonConstant * shape) +
      (comparisonConstant * (shape + reference) + comparisonConstant * reference +
        (stable + 2 * reference)) * stable ≤
      4 * (comparisonConstant + 1) * ((shape + reference) * stable + reference * shape) := by
    have squareBound := mul_le_mul_of_nonneg_right stableBelow stableNonnegative
    nlinarith [mul_nonneg comparisonNonnegative (mul_nonneg referenceNonnegative stableNonnegative),
      mul_nonneg comparisonNonnegative (mul_nonneg shapeNonnegative stableNonnegative),
      mul_nonneg comparisonNonnegative (mul_nonneg referenceNonnegative shapeNonnegative),
      mul_nonneg referenceNonnegative stableNonnegative, mul_nonneg referenceNonnegative shapeNonnegative]
  change |(localNormalFormError 1 graph coordinate first).2 -
      (localNormalFormError 1 graph coordinate second).2| ≤
      constant * ((shape + reference) * stable + reference * shape)
  rw [errorIdentity first firstSmall, errorIdentity second secondSmall]
  apply enlarged.trans
  exact (mul_le_mul_of_nonneg_left scalar fiberNonnegative).trans (by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_right constantBound
      (add_nonneg (mul_nonneg (add_nonneg shapeNonnegative referenceNonnegative) stableNonnegative)
        (mul_nonneg referenceNonnegative shapeNonnegative)))

end EulerNonuniqueness.Section6
