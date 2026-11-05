import EulerNonuniqueness.Section6.NormalFormInverseMatching
import EulerNonuniqueness.Section6.SameGraphPhaseCorrection

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem localNormalFormChart_exists_uniform_comparison
    {baseGraph baseCoordinate outputGraph outputCoordinate : ℝ → ℝ}
    (baseGraphAnalytic : AnalyticAt ℝ baseGraph 0)
    (baseCoordinateSmooth : ContDiffAt ℝ 2 baseCoordinate 0)
    (baseGraphZero : baseGraph 0 = 0) (baseCoordinateZero : baseCoordinate 0 = 0)
    (baseGraphDerivative : HasDerivAt baseGraph 0 0)
    (baseCoordinateDerivative : HasDerivAt baseCoordinate 1 0)
    (outputGraphAnalytic : AnalyticAt ℝ outputGraph 0)
    (outputCoordinateSmooth : ContDiffAt ℝ 2 outputCoordinate 0)
    (outputGraphZero : outputGraph 0 = 0) (outputCoordinateZero : outputCoordinate 0 = 0)
    (outputGraphDerivative : HasDerivAt outputGraph 0 0)
    (outputCoordinateDerivative : HasDerivAt outputCoordinate 1 0) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ), ∀ first second : ℝ × ℝ,
      |first.1| + |first.2| < radius → |second.1| + |second.2| < radius →
      |(localNormalFormChart outputGraph outputCoordinate first).1 -
          (localNormalFormChart outputGraph outputCoordinate second).1| +
        |(localNormalFormChart outputGraph outputCoordinate first).2 -
          (localNormalFormChart outputGraph outputCoordinate second).2| +
        |(phaseCorrection 1 outputGraph first.1 - phaseCorrection 1 baseGraph first.1) -
          (phaseCorrection 1 outputGraph second.1 - phaseCorrection 1 baseGraph second.1)| ≤
        constant *
          (|(localNormalFormChart baseGraph baseCoordinate first).1 -
              (localNormalFormChart baseGraph baseCoordinate second).1| +
            |(localNormalFormChart baseGraph baseCoordinate first).2 -
              (localNormalFormChart baseGraph baseCoordinate second).2|) := by
  have baseGraphSmooth : ContDiffAt ℝ 2 baseGraph 0 := baseGraphAnalytic.contDiffAt
  have outputGraphSmooth : ContDiffAt ℝ 2 outputGraph 0 := outputGraphAnalytic.contDiffAt
  obtain ⟨inverseRadius, inverseRadiusPositive, inverseConstant, inverseConstantBound, inverseEstimate⟩ :=
    localNormalFormChart_exists_uniform_inverse_lipschitz baseGraphSmooth baseCoordinateSmooth
      baseGraphZero baseCoordinateZero baseGraphDerivative baseCoordinateDerivative
  have basePhaseSmooth := (sameGraph_phaseCorrection_exists_uniform_stable_factor
    baseGraphAnalytic baseGraphZero baseGraphDerivative baseCoordinateZero baseCoordinateDerivative).1
  have outputPhaseSmooth := (sameGraph_phaseCorrection_exists_uniform_stable_factor
    outputGraphAnalytic outputGraphZero outputGraphDerivative outputCoordinateZero outputCoordinateDerivative).1
  have outputRegular := localNormalFormChart_regular outputGraphSmooth outputCoordinateSmooth
    outputGraphZero outputCoordinateZero outputGraphDerivative outputCoordinateDerivative
  let augmented : (ℝ × ℝ) → (ℝ × ℝ) × ℝ := fun point =>
    (localNormalFormChart outputGraph outputCoordinate point,
      phaseCorrection 1 outputGraph point.1 - phaseCorrection 1 baseGraph point.1)
  have correctionSmooth : ContDiffAt ℝ 2
      (fun point : ℝ × ℝ => phaseCorrection 1 outputGraph point.1 -
        phaseCorrection 1 baseGraph point.1) 0 :=
    (ContDiffAt.comp (f := Prod.fst) (g := phaseCorrection 1 outputGraph) 0
      outputPhaseSmooth contDiffAt_fst).sub
      (ContDiffAt.comp (f := Prod.fst) (g := phaseCorrection 1 baseGraph) 0
        basePhaseSmooth contDiffAt_fst)
  have augmentedSmooth : ContDiffAt ℝ 1 augmented 0 :=
    (outputRegular.1.prodMk correctionSmooth).of_le (by norm_num)
  obtain ⟨outputBound, region, regionMem, outputLipschitz⟩ := augmentedSmooth.exists_lipschitzOnWith
  obtain ⟨outputRadius, outputRadiusPositive, inside⟩ := Metric.mem_nhds_iff.mp regionMem
  have coefficientNonnegative : 0 ≤ 3 * (outputBound : ℝ) * inverseConstant :=
    mul_nonneg (mul_nonneg (by norm_num) outputBound.coe_nonneg) (by linarith)
  refine ⟨min inverseRadius outputRadius, lt_min inverseRadiusPositive outputRadiusPositive,
    3 * (outputBound : ℝ) * inverseConstant + 1, by linarith, ?_⟩
  intro first second firstSmall secondSmall
  have norm_le_sum (point : ℝ × ℝ) : ‖point‖ ≤ |point.1| + |point.2| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg point.2))
      (le_add_of_nonneg_left (abs_nonneg point.1))
  have pointInside (point : ℝ × ℝ)
      (small : |point.1| + |point.2| < min inverseRadius outputRadius) : point ∈ region := by
    apply inside
    rw [Metric.mem_ball, dist_zero_right]
    exact (norm_le_sum point).trans_lt (small.trans_le (min_le_right _ _))
  have forward := outputLipschitz.dist_le_mul _ (pointInside first firstSmall)
    _ (pointInside second secondSmall)
  rw [dist_eq_norm, dist_eq_norm] at forward
  have inverse := inverseEstimate first second
    (firstSmall.trans_le (min_le_left _ _)) (secondSmall.trans_le (min_le_left _ _))
  have physicalInverse : ‖first - second‖ ≤ inverseConstant *
      ‖localNormalFormChart baseGraph baseCoordinate first -
        localNormalFormChart baseGraph baseCoordinate second‖ :=
    (norm_le_sum (first - second)).trans inverse
  have augmentedEstimate : ‖augmented first - augmented second‖ ≤
      (outputBound : ℝ) * inverseConstant *
        ‖localNormalFormChart baseGraph baseCoordinate first -
          localNormalFormChart baseGraph baseCoordinate second‖ := by
    exact forward.trans (by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left physicalInverse outputBound.coe_nonneg)
  have chartNorm : ‖localNormalFormChart outputGraph outputCoordinate first -
      localNormalFormChart outputGraph outputCoordinate second‖ ≤ ‖augmented first - augmented second‖ :=
    norm_fst_le (augmented first - augmented second)
  have firstComponent := (norm_fst_le
    (localNormalFormChart outputGraph outputCoordinate first -
      localNormalFormChart outputGraph outputCoordinate second)).trans chartNorm
  have secondComponent := (norm_snd_le
    (localNormalFormChart outputGraph outputCoordinate first -
      localNormalFormChart outputGraph outputCoordinate second)).trans chartNorm
  have phaseComponent := norm_snd_le (augmented first - augmented second)
  have baseNorm := norm_le_sum (localNormalFormChart baseGraph baseCoordinate first -
    localNormalFormChart baseGraph baseCoordinate second)
  simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs] at firstComponent secondComponent baseNorm
  change |(phaseCorrection 1 outputGraph first.1 - phaseCorrection 1 baseGraph first.1) -
    (phaseCorrection 1 outputGraph second.1 - phaseCorrection 1 baseGraph second.1)| ≤
    ‖augmented first - augmented second‖ at phaseComponent
  have enlarged := mul_le_mul_of_nonneg_left baseNorm coefficientNonnegative
  have baseNonnegative := add_nonneg
    (abs_nonneg ((localNormalFormChart baseGraph baseCoordinate first).1 -
      (localNormalFormChart baseGraph baseCoordinate second).1))
    (abs_nonneg ((localNormalFormChart baseGraph baseCoordinate first).2 -
      (localNormalFormChart baseGraph baseCoordinate second).2))
  nlinarith

end EulerNonuniqueness.Section6
