import EulerNonuniqueness.Section6.NormalFormRemainder
import EulerNonuniqueness.General.FiberPrimitiveLipschitz

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem exists_localNormalForm_graded_relative_remainder :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ first second : ℝ × ℝ,
      |first.1| + |first.2| < radius → |second.1| + |second.2| < radius →
      ‖localNormalFormError 1 graph coordinate (first.1, graph first.1 + first.2) -
          localNormalFormError 1 graph coordinate (second.1, graph second.1 + second.2)‖ ≤
        constant * ((|first.2| + |second.2|) * |first.1 - second.1| +
          (|first.1| + |second.1| + |first.2| + |second.2|) * |first.2 - second.2|) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, normalForm⟩ := localNormalForm_on_separatrix_exists 1 (by norm_num)
  have coefficientRegular := localNormalFormCoefficient_regular 1 (graphAnalytic.contDiffAt (n := 2))
    coordinateSmooth graphDerivative coordinateDerivative
  obtain ⟨coefficientBound, coefficientRegion, coefficientRegionMem, coefficientLipschitz⟩ :=
    coefficientRegular.1.exists_lipschitzOnWith
  obtain ⟨graphBound, graphRegion, graphRegionMem, graphLipschitz⟩ :=
    (graphAnalytic.contDiffAt (n := 1)).exists_lipschitzOnWith
  have vanishing : ∀ᶠ unstable in nhds (0 : ℝ), localNormalFormError 1 graph coordinate (unstable, graph unstable) = 0 := by
    filter_upwards [normalForm] with unstable identity
    unfold localNormalFormError
    rw [identity.1, identity.2]
    simp
  obtain ⟨coefficientRadius, coefficientPositive, coefficientInside⟩ := Metric.mem_nhds_iff.mp
    (inter_mem coefficientRegionMem (localNormalFormError_vertical_derivative 1 graph coordinate))
  obtain ⟨graphRadius, graphPositive, graphInside⟩ := Metric.mem_nhds_iff.mp (inter_mem graphRegionMem vanishing)
  let radius := min graphRadius (coefficientRadius / (1 + (graphBound : ℝ)))
  let constant := (coefficientBound : ℝ) * (1 + (graphBound : ℝ))
  have multiplierPositive : 0 < 1 + (graphBound : ℝ) := by positivity
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have zeroGraphInside : (0 : ℝ) ∈ Metric.ball 0 graphRadius := by simpa only [Metric.mem_ball, dist_self] using graphPositive
  have zeroCoefficientInside : (0 : ℝ × ℝ) ∈ Metric.ball 0 coefficientRadius := by simpa only [Metric.mem_ball, dist_self] using coefficientPositive
  have graphMember (unstable : ℝ) (small : |unstable| < radius) : unstable ∈ Metric.ball (0 : ℝ) graphRadius := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using small.trans_le (min_le_left _ _)
  have graphSize (unstable : ℝ) (small : |unstable| < radius) : |graph unstable| ≤ (graphBound : ℝ) * |unstable| := by
    have actual := (lipschitzOnWith_iff_norm_sub_le.mp graphLipschitz) (graphInside (graphMember unstable small)).1
      (graphInside zeroGraphInside).1
    simpa only [graphZero, sub_zero, Real.norm_eq_abs] using actual
  have pathInside (point : ℝ × ℝ) (small : |point.1| + |point.2| < radius)
      (parameter : ℝ) (member : parameter ∈ Icc (0 : ℝ) 1) :
      (point.1, graph point.1 + parameter * point.2) ∈ Metric.ball (0 : ℝ × ℝ) coefficientRadius := by
    have unstableSmall : |point.1| < radius := lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg point.2)) small
    have size := graphSize point.1 unstableSmall
    have parameterBound : |parameter| ≤ 1 := by rw [abs_of_nonneg member.1]; exact member.2
    have stableBound := (abs_add (graph point.1) (parameter * point.2)).trans
      (add_le_add size (by simpa only [abs_mul, one_mul] using mul_le_mul_of_nonneg_right parameterBound (abs_nonneg point.2)))
    have productBound : (1 + (graphBound : ℝ)) * (|point.1| + |point.2|) < coefficientRadius := by
      apply (mul_lt_mul_of_pos_left small multiplierPositive).trans_le
      have actual := mul_le_mul_of_nonneg_left (min_le_right graphRadius (coefficientRadius / (1 + (graphBound : ℝ)))) multiplierPositive.le
      dsimp only [radius]
      simpa only [mul_div_cancel₀ _ multiplierPositive.ne'] using actual
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    apply max_lt
    · have extra : 0 ≤ (graphBound : ℝ) * |point.1| + (1 + (graphBound : ℝ)) * |point.2| := by positivity
      nlinarith only [productBound, extra]
    · have extra : 0 ≤ |point.1| + (graphBound : ℝ) * |point.2| := by positivity
      nlinarith only [productBound, stableBound, extra]
  have factorIdentity (point : ℝ × ℝ) (small : |point.1| + |point.2| < radius) :
      localNormalFormError 1 graph coordinate (point.1, graph point.1 + point.2) =
        point.2 • fiberPrimitive (localNormalFormCoefficient 1 graph coordinate) graph point := by
    have unstableSmall : |point.1| < radius := lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg point.2)) small
    apply fiber_primitive_identity point (graphInside (graphMember point.1 unstableSmall)).2
    · apply coefficientLipschitz.continuousOn.comp (by fun_prop)
      exact fun parameter member => (coefficientInside (pathInside point small parameter member)).1
    · intro parameter member
      exact (coefficientInside (pathInside point small parameter member)).2
  have factorDifference (first second : ℝ × ℝ) (firstSmall : |first.1| + |first.2| < radius)
      (secondSmall : |second.1| + |second.2| < radius) :
      ‖fiberPrimitive (localNormalFormCoefficient 1 graph coordinate) graph first -
        fiberPrimitive (localNormalFormCoefficient 1 graph coordinate) graph second‖ ≤
        constant * (|first.1 - second.1| + |first.2 - second.2|) := by
    have graphDifference := (lipschitzOnWith_iff_norm_sub_le.mp graphLipschitz)
      (graphInside (graphMember first.1 (lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg first.2)) firstSmall))).1
      (graphInside (graphMember second.1 (lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg second.2)) secondSmall))).1
    have actual := fiberPrimitive_lipschitz_between first second coefficientLipschitz graphBound.coe_nonneg
      (by simpa only [Real.norm_eq_abs] using graphDifference)
      (fun parameter member => (coefficientInside (pathInside first firstSmall parameter member)).1)
      (fun parameter member => (coefficientInside (pathInside second secondSmall parameter member)).1)
    apply actual.trans
    have extra : 0 ≤ (coefficientBound : ℝ) * (graphBound : ℝ) * |first.2 - second.2| := by positivity
    dsimp only [constant]
    nlinarith only [extra]
  have factorZero := fiberPrimitive_zero (localNormalFormCoefficient 1 graph coordinate) graph graphZero coefficientRegular.2
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    constant, by dsimp only [constant]; positivity, radius, radiusPositive, ?_⟩
  intro first second firstSmall secondSmall
  rw [factorIdentity first firstSmall, factorIdentity second secondSmall]
  have firstBound := factorDifference first 0 firstSmall (by simpa only [Prod.fst_zero, Prod.snd_zero, abs_zero, zero_add] using radiusPositive)
  rw [factorZero, sub_zero] at firstBound
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at firstBound
  exact graded_fiber_product_difference (by dsimp only [constant]; positivity) firstBound (factorDifference first second firstSmall secondSmall)

end EulerNonuniqueness.Section6
