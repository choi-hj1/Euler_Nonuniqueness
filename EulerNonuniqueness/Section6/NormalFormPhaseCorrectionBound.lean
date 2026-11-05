import EulerNonuniqueness.Section6.NormalFormInverseMatching
import EulerNonuniqueness.Section6.PhaseStraightening

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem localNormalFormChart_exists_uniform_phase_correction_bound
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ), ∀ first second : ℝ × ℝ,
      |first.1| + |first.2| < radius → |second.1| + |second.2| < radius →
      |((Real.sqrt 2 - 1) / 4) * (shapeChartAngle first - shapeChartAngle second)| +
        |phaseCorrection 1 graph first.1 - phaseCorrection 1 graph second.1| ≤
          constant *
            (|(localNormalFormChart graph coordinate first).1 - (localNormalFormChart graph coordinate second).1| +
              |(localNormalFormChart graph coordinate first).2 - (localNormalFormChart graph coordinate second).2|) := by
  obtain ⟨inverseRadius, inverseRadiusPositive, inverseConstant, inverseOne, inverseEstimate⟩ :=
    localNormalFormChart_exists_uniform_inverse_lipschitz graphAnalytic.contDiffAt coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  have phaseSmooth := (phaseCorrection_regular 1 (by norm_num) graphAnalytic graphZero graphDerivative).1
  let correction : (ℝ × ℝ) → ℝ × ℝ := fun point =>
    (((Real.sqrt 2 - 1) / 4) * shapeChartAngle point, phaseCorrection 1 graph point.1)
  have angleSmooth : ContDiffAt ℝ 2 (fun point : ℝ × ℝ =>
      ((Real.sqrt 2 - 1) / 4) * shapeChartAngle point) 0 := by
    unfold shapeChartAngle
    fun_prop
  have phasePointSmooth : ContDiffAt ℝ 2 (fun point : ℝ × ℝ => phaseCorrection 1 graph point.1) 0 :=
    ContDiffAt.comp (f := Prod.fst) (g := phaseCorrection 1 graph) 0 phaseSmooth contDiffAt_fst
  have correctionSmooth : ContDiffAt ℝ 1 correction 0 :=
    (angleSmooth.prodMk phasePointSmooth).of_le (by norm_num)
  obtain ⟨correctionBound, region, regionMem, correctionLipschitz⟩ := correctionSmooth.exists_lipschitzOnWith
  obtain ⟨correctionRadius, correctionRadiusPositive, inside⟩ := Metric.mem_nhds_iff.mp regionMem
  have coefficientNonnegative : 0 ≤ 2 * (correctionBound : ℝ) * inverseConstant :=
    mul_nonneg (mul_nonneg (by norm_num) correctionBound.coe_nonneg) (zero_le_one.trans inverseOne)
  refine ⟨min inverseRadius correctionRadius, lt_min inverseRadiusPositive correctionRadiusPositive,
    2 * (correctionBound : ℝ) * inverseConstant + 1, by linarith only [coefficientNonnegative], ?_⟩
  intro first second firstSmall secondSmall
  have norm_le_sum (point : ℝ × ℝ) : ‖point‖ ≤ |point.1| + |point.2| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg point.2))
      (le_add_of_nonneg_left (abs_nonneg point.1))
  have pointInside (point : ℝ × ℝ)
      (small : |point.1| + |point.2| < min inverseRadius correctionRadius) : point ∈ region := by
    apply inside
    rw [Metric.mem_ball, dist_zero_right]
    exact (norm_le_sum point).trans_lt (small.trans_le (min_le_right _ _))
  have forward := correctionLipschitz.dist_le_mul _ (pointInside first firstSmall)
    _ (pointInside second secondSmall)
  rw [dist_eq_norm, dist_eq_norm] at forward
  have physicalInverse := (norm_le_sum (first - second)).trans
    (inverseEstimate first second (firstSmall.trans_le (min_le_left _ _))
      (secondSmall.trans_le (min_le_left _ _)))
  have correctionEstimate : ‖correction first - correction second‖ ≤
      (correctionBound : ℝ) * inverseConstant *
        ‖localNormalFormChart graph coordinate first - localNormalFormChart graph coordinate second‖ := by
    exact forward.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left physicalInverse correctionBound.coe_nonneg)
  have firstComponent := norm_fst_le (correction first - correction second)
  have secondComponent := norm_snd_le (correction first - correction second)
  change |((Real.sqrt 2 - 1) / 4) * shapeChartAngle first -
    ((Real.sqrt 2 - 1) / 4) * shapeChartAngle second| ≤ ‖correction first - correction second‖ at firstComponent
  rw [← mul_sub] at firstComponent
  change |phaseCorrection 1 graph first.1 - phaseCorrection 1 graph second.1| ≤
    ‖correction first - correction second‖ at secondComponent
  have chartNorm := norm_le_sum (localNormalFormChart graph coordinate first - localNormalFormChart graph coordinate second)
  simp only [Prod.fst_sub, Prod.snd_sub] at chartNorm
  have enlarged := mul_le_mul_of_nonneg_left chartNorm coefficientNonnegative
  have chartNonnegative := add_nonneg
    (abs_nonneg ((localNormalFormChart graph coordinate first).1 - (localNormalFormChart graph coordinate second).1))
    (abs_nonneg ((localNormalFormChart graph coordinate first).2 - (localNormalFormChart graph coordinate second).2))
  nlinarith only [firstComponent, secondComponent, correctionEstimate, enlarged, chartNonnegative]

end EulerNonuniqueness.Section6
