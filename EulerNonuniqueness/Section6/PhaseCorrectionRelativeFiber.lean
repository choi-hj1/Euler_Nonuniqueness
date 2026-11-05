import EulerNonuniqueness.Section6.SameGraphPhaseCorrection
import EulerNonuniqueness.General.FiberPrimitiveLipschitz

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem sameGraph_phaseCorrection_exists_graded_relative_fiber_bound
    {graph : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0) :
    ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ first second : ℝ × ℝ,
      |first.1| + |first.2| < radius → |second.1| + |second.2| < radius →
      |correctedPhaseError 1 (phaseCorrection 1 graph) (first.1, graph first.1 + first.2) -
        correctedPhaseError 1 (phaseCorrection 1 graph) (second.1, graph second.1 + second.2)| ≤
        constant * ((|first.2| + |second.2|) * |first.1 - second.1| +
          (|first.1| + |second.1| + |first.2| + |second.2|) * |first.2 - second.2|) := by
  have regular := phaseCorrection_regular 1 (by norm_num) graphAnalytic graphZero graphDerivative
  have coefficientRegular := correctedPhaseCoefficient_regular 1 regular.1 regular.2.2.1
  obtain ⟨coefficientBound, coefficientRegion, coefficientRegionMem, coefficientLipschitz⟩ :=
    coefficientRegular.1.exists_lipschitzOnWith
  obtain ⟨graphBound, graphRegion, graphRegionMem, graphLipschitz⟩ :=
    (graphAnalytic.contDiffAt (n := 1)).exists_lipschitzOnWith
  have vanishing : ∀ᶠ unstable in 𝓝 (0 : ℝ),
      correctedPhaseError 1 (phaseCorrection 1 graph) (unstable, graph unstable) = 0 := by
    filter_upwards [regular.2.2.2] with unstable identity
    exact sub_eq_zero.mpr identity.symm
  obtain ⟨coefficientRadius, coefficientPositive, coefficientInside⟩ := Metric.mem_nhds_iff.mp
    (inter_mem coefficientRegionMem (correctedPhaseError_vertical_derivative 1 (phaseCorrection 1 graph)))
  obtain ⟨graphRadius, graphPositive, graphInside⟩ := Metric.mem_nhds_iff.mp (inter_mem graphRegionMem vanishing)
  let radius := min graphRadius (coefficientRadius / (1 + (graphBound : ℝ)))
  let constant := (coefficientBound : ℝ) * (1 + (graphBound : ℝ))
  have multiplierPositive : 0 < 1 + (graphBound : ℝ) := by positivity
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have zeroGraphInside : (0 : ℝ) ∈ Metric.ball 0 graphRadius := by simpa using graphPositive
  have zeroCoefficientInside : (0 : ℝ × ℝ) ∈ Metric.ball 0 coefficientRadius := by simpa using coefficientPositive
  have graphMember (unstable : ℝ) (small : |unstable| < radius) : unstable ∈ Metric.ball (0 : ℝ) graphRadius := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using small.trans_le (min_le_left _ _)
  have graphSize (unstable : ℝ) (small : |unstable| < radius) : |graph unstable| ≤ (graphBound : ℝ) * |unstable| := by
    have actual := (lipschitzOnWith_iff_norm_sub_le.mp graphLipschitz) (graphInside (graphMember unstable small)).1
      (graphInside zeroGraphInside).1
    simpa only [graphZero, sub_zero, Real.norm_eq_abs] using actual
  have pathInside (point : ℝ × ℝ) (small : |point.1| + |point.2| < radius)
      (parameter : ℝ) (member : parameter ∈ Icc (0 : ℝ) 1) :
      (point.1, graph point.1 + parameter * point.2) ∈ Metric.ball (0 : ℝ × ℝ) coefficientRadius := by
    have unstableSmall : |point.1| < radius := (le_add_of_nonneg_right (abs_nonneg _)).trans_lt small
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
      correctedPhaseError 1 (phaseCorrection 1 graph) (point.1, graph point.1 + point.2) =
        point.2 • fiberPrimitive (correctedPhaseCoefficient 1 (phaseCorrection 1 graph)) graph point := by
    have unstableSmall : |point.1| < radius := (le_add_of_nonneg_right (abs_nonneg _)).trans_lt small
    apply fiber_primitive_identity point (graphInside (graphMember point.1 unstableSmall)).2
    · apply coefficientLipschitz.continuousOn.comp (by fun_prop)
      exact fun parameter member => (coefficientInside (pathInside point small parameter member)).1
    · intro parameter member
      exact (coefficientInside (pathInside point small parameter member)).2
  have factorDifference (first second : ℝ × ℝ) (firstSmall : |first.1| + |first.2| < radius)
      (secondSmall : |second.1| + |second.2| < radius) :
      ‖fiberPrimitive (correctedPhaseCoefficient 1 (phaseCorrection 1 graph)) graph first -
        fiberPrimitive (correctedPhaseCoefficient 1 (phaseCorrection 1 graph)) graph second‖ ≤
        constant * (|first.1 - second.1| + |first.2 - second.2|) := by
    have graphDifference := (lipschitzOnWith_iff_norm_sub_le.mp graphLipschitz)
      (graphInside (graphMember first.1 ((le_add_of_nonneg_right (abs_nonneg _)).trans_lt firstSmall))).1
      (graphInside (graphMember second.1 ((le_add_of_nonneg_right (abs_nonneg _)).trans_lt secondSmall))).1
    have actual := fiberPrimitive_lipschitz_between first second coefficientLipschitz graphBound.coe_nonneg
      (by simpa only [Real.norm_eq_abs] using graphDifference)
      (fun parameter member => (coefficientInside (pathInside first firstSmall parameter member)).1)
      (fun parameter member => (coefficientInside (pathInside second secondSmall parameter member)).1)
    apply actual.trans
    have extra : 0 ≤ (coefficientBound : ℝ) * (graphBound : ℝ) * |first.2 - second.2| := by positivity
    dsimp only [constant]
    nlinarith only [extra]
  have factorZero := fiberPrimitive_zero (correctedPhaseCoefficient 1 (phaseCorrection 1 graph)) graph graphZero coefficientRegular.2
  refine ⟨constant, by dsimp only [constant]; positivity, radius, radiusPositive, ?_⟩
  intro first second firstSmall secondSmall
  rw [factorIdentity first firstSmall, factorIdentity second secondSmall]
  have firstBound := factorDifference first 0 firstSmall (by simpa using radiusPositive)
  rw [factorZero, sub_zero] at firstBound
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at firstBound
  exact graded_fiber_product_difference (by dsimp only [constant]; positivity) firstBound (factorDifference first second firstSmall secondSmall)

end EulerNonuniqueness.Section6
