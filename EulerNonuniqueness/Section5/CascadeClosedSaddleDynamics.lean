import EulerNonuniqueness.Section5.CascadeCoherentSaddleDynamics
import EulerNonuniqueness.Section4.ReferencePaperShapeDerivative

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem CascadeInternallyStoppedPath.paired_shape_hasDerivAt_on_closed_prefix
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared) {time : ℝ} (inside : time ∈ Icc 0 path.stop)
    (side : Fin 2) (index : Fin count)
    (small : |unstableShape (cascadePairedMotion prepared side) time index| +
      |stableShape (cascadePairedMotion prepared side) time index| ≤ 1 / 4) :
    HasDerivAt (fun current => (unstableShape (cascadePairedMotion prepared side) current index,
        stableShape (cascadePairedMotion prepared side) current index))
      (referencePointShapeVelocity scales (cascadePairedMotion prepared side) time index) time := by
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have upper := paper_shape_ratio_im_pos_of_small (cascadePairedMotion prepared side) time index small
  fin_cases side
  · exact prepared.trajectory.movingFamily.centroid_paper_shape_hasDerivAt_of_upper path.evolution inside index
      (fun _ => globalInside) (fun patch label => path.material_boundary inside (finProdFinEquiv (index, patch)) label)
      upper small
  · simp only [cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] at small upper ⊢
    apply prepared.referenceWitness.trajectory.movingFamily.centroid_paper_shape_hasDerivAt_of_upper
      (prepared.referenceWitness.evolution.mono (show path.stop ≤ 2 by linarith [path.stopBound])) inside index
      (fun _ => globalInside) ?_ upper small
    intro patch label
    rw [prepared.referenceWitness.trajectory.movingFamily.patchVorticity_eq scales prepared.referenceWitness.densityIdentity]
    exact prepared.referenceWitness.trajectory.movingFamily_material_equation_of_margin prepared.referenceWitness.marginPositive
      globalInside (prepared.referenceWitness.safe time ⟨inside.1, by linarith [inside.2, path.stopBound]⟩)
      (finProdFinEquiv (index, patch)) label

theorem exists_uniform_cascade_closed_saddle_dynamics {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
    ∀ {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, ∀ time ∈ Icc 0 path.stop,
    (∀ side, |unstableShape (cascadePairedMotion prepared side) time index| +
      |stableShape (cascadePairedMotion prepared side) time index| < radius) →
    HasDerivAt (fun current => referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index current -
        referenceStraightenedShape prepared.reference graph coordinate index current)
      (relativeStraightenedSaddleVelocity scales (cascadePairedMotion prepared) graph coordinate index time) time := by
  have nearby := ((graphSmooth.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)).eventually (by norm_num)).and
    ((coordinateSmooth.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)).eventually (by norm_num))
  obtain ⟨baseRadius, basePositive, baseInside⟩ := Metric.mem_nhds_iff.mp nearby
  let radius := min baseRadius (1 / 4)
  refine ⟨radius, by dsimp [radius]; positivity, min_le_right _ _, ?_⟩
  intro scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor
    boundaryConstant count prepared path index time inside small
  let frequency := fun side => scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 /
    diagonalDifference (cascadePairedMotion prepared side) time index
  let chart := fun side => referenceStraightenedShape (cascadePairedMotion prepared side) graph coordinate index time
  let error := fun side => localNormalFormError 1 graph coordinate
    (unstableShape (cascadePairedMotion prepared side) time index, stableShape (cascadePairedMotion prepared side) time index)
  let forcing := fun side => referenceStraightenedForcing scales (cascadePairedMotion prepared side) graph coordinate index time
  have equations (side : Fin 2) : HasDerivAt
      (referenceStraightenedShape (cascadePairedMotion prepared side) graph coordinate index)
      ((2 * Real.sqrt 2 * frequency side * (chart side).1,
        -(2 * Real.sqrt 2 * frequency side) * (chart side).2) + frequency side • error side + forcing side) time := by
    have derivatives := baseInside
      (show unstableShape (cascadePairedMotion prepared side) time index ∈ Metric.ball (0 : ℝ) baseRadius by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
        exact (le_add_of_nonneg_right (abs_nonneg _)).trans_lt ((small side).trans_le (min_le_left _ _)))
    have raw := path.paired_shape_hasDerivAt_on_closed_prefix inside side index
      ((small side).le.trans (min_le_right _ _))
    change HasDerivAt
      (fun current => (unstableShape (cascadePairedMotion prepared side) current index,
        stableShape (cascadePairedMotion prepared side) current index))
      (shapeChartVelocity (frequency side) (unstableShape (cascadePairedMotion prepared side) time index,
        stableShape (cascadePairedMotion prepared side) time index) +
          referencePointShapeForcing scales (cascadePairedMotion prepared side) time index) time at raw
    have actual := localNormalFormChart_forced_equation raw
      (derivatives.1.differentiableAt (by norm_num)) (derivatives.2.differentiableAt (by norm_num))
    rw [localNormalFormError_frequency_smul] at actual
    convert actual using 1 <;>
      dsimp only [referenceStraightenedShape, referenceStraightenedForcing, frequency, chart, error, forcing,
        Prod.add_def, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ext <;> ring
  have actual := (equations 0).sub (equations 1)
  convert actual using 1 <;>
    dsimp only [relativeStraightenedSaddleVelocity, frequency, chart, error, forcing, cascadePairedMotion,
      Fin.cases_zero, Fin.cases_succ, Prod.add_def, Prod.sub_def, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ext <;> ring

end EulerNonuniqueness.Paper
