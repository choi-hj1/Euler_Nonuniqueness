import EulerNonuniqueness.Section5.CascadeCoherentSaddleDynamics
import EulerNonuniqueness.Section6.NormalFormErrorLinearBound
import EulerNonuniqueness.Section6.DilationFrequencySaddleError
import EulerNonuniqueness.Section6.SourcePacketRhombusJointContinuation

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def relativeStraightenedSaddlePointRemainder {count : ℕ} (scales : Scales)
    (motion : Fin 2 → PatchMotion count) (graph coordinate : ℝ → ℝ) (index : Fin count) (time : ℝ) : ℝ × ℝ :=
  let dilation := fun side => diagonalDifference (motion side) time index / scales.length (index.val + 1) ^ 2
  let chart := fun side => referenceStraightenedShape (motion side) graph coordinate index time
  let error := fun side => localNormalFormError 1 graph coordinate
    (unstableShape (motion side) time index, stableShape (motion side) time index)
  dilationFrequencySaddleError (scales.omega (index.val + 1)) (dilation 0) (dilation 1) (chart 0) (chart 1) +
    (scales.omega (index.val + 1) / dilation 0) • (error 0 - error 1) +
    (scales.omega (index.val + 1) / dilation 0 - scales.omega (index.val + 1) / dilation 1) • error 1

def relativeStraightenedSaddlePointBudget {count : ℕ} (scales : Scales)
    (motion : Fin 2 → PatchMotion count) (graph coordinate : ℝ → ℝ)
    (constant referenceConstant : ℝ) (index : Fin count) (time : ℝ) : ℝ :=
  let dilation := fun side => diagonalDifference (motion side) time index / scales.length (index.val + 1) ^ 2
  let chart := fun side => referenceStraightenedShape (motion side) graph coordinate index time
  let difference := |(chart 0).1 - (chart 1).1| + |(chart 0).2 - (chart 1).2|
  let referenceSize := |(chart 1).1| + |(chart 1).2|
  2 * Real.sqrt 2 *
      (2 * |scales.omega (index.val + 1)| * |dilation 0 - 1| * difference +
        4 * |scales.omega (index.val + 1)| * |dilation 0 - dilation 1| * referenceSize) +
    2 * |scales.omega (index.val + 1)| *
      (constant * difference * (|(chart 0).2 - (chart 1).2| + |(chart 1).1| + |(chart 1).2|)) +
    (4 * |scales.omega (index.val + 1)| * |dilation 0 - dilation 1|) * (referenceConstant * referenceSize)

theorem relativeStraightenedSaddleVelocity_eq_pointRemainder {count : ℕ} (scales : Scales)
    (motion : Fin 2 → PatchMotion count) (graph coordinate : ℝ → ℝ) (index : Fin count) (time : ℝ) :
    relativeStraightenedSaddleVelocity scales motion graph coordinate index time =
      (2 * Real.sqrt 2 * scales.omega (index.val + 1) *
          ((referenceStraightenedShape (motion 0) graph coordinate index time).1 -
            (referenceStraightenedShape (motion 1) graph coordinate index time).1),
        -(2 * Real.sqrt 2 * scales.omega (index.val + 1)) *
          ((referenceStraightenedShape (motion 0) graph coordinate index time).2 -
            (referenceStraightenedShape (motion 1) graph coordinate index time).2)) +
      relativeStraightenedSaddlePointRemainder scales motion graph coordinate index time +
      (referenceStraightenedForcing scales (motion 0) graph coordinate index time -
        referenceStraightenedForcing scales (motion 1) graph coordinate index time) := by
  simp only [relativeStraightenedSaddleVelocity, relativeStraightenedSaddlePointRemainder,
    dilationFrequencySaddleError, div_div_eq_mul_div]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem exists_uniform_cascade_saddle_point_remainder :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ constant ≥ (0 : ℝ), ∃ referenceConstant ≥ (1 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {scaleRoot boundaryConstant factor threshold coarseConstant : ℝ},
      0 < scaleRoot → 0 ≤ boundaryConstant → 0 < factor → factor ≤ 1 / 8 →
      threshold ≤ 1 / 8 → 0 ≤ coarseConstant →
      ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {shapeRadius monitor : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold coarseConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared,
      ∀ index : Fin count, index.val + 1 < count → ∀ time ∈ Ioo 0 path.stop,
      (∀ side, ∀ current ∈ Icc 0 time,
        |unstableShape (cascadePairedMotion prepared side) current index| +
          |stableShape (cascadePairedMotion prepared side) current index| < radius) →
      HasDerivAt (fun current => referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index current -
          referenceStraightenedShape prepared.reference graph coordinate index current)
        (relativeStraightenedSaddleVelocity {scales with frequency := frequency}
          (cascadePairedMotion prepared) graph coordinate index time) time ∧
      ‖relativeStraightenedSaddlePointRemainder {scales with frequency := frequency}
          (cascadePairedMotion prepared) graph coordinate index time‖ ≤
        relativeStraightenedSaddlePointBudget {scales with frequency := frequency}
          (cascadePairedMotion prepared) graph coordinate constant referenceConstant index time := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, constant, constantNonnegative, baseRadius, basePositive, baseSmall, compatible, dynamics⟩ :=
    exists_uniform_cascade_coherent_saddle_dynamics
  obtain ⟨errorRadius, errorPositive, referenceConstant, referenceOne, errorBound⟩ :=
    localNormalFormError_exists_uniform_linear_chart_bound (graphAnalytic.contDiffAt (n := 2)) coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  let radius := min baseRadius errorRadius
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, constant, constantNonnegative, referenceConstant, referenceOne, radius,
    lt_min basePositive errorPositive, (min_le_left _ _).trans baseSmall, compatible, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold coarseConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall coarseNonnegative
  filter_upwards [dynamics scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      factorPositive (by linarith : factor ≤ 1) thresholdSmall coarseNonnegative,
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative]
    with frequency dynamics joint
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal time inside small
  let changed : Scales := {scales with frequency := frequency}
  have endpoint (side : Fin 2) := small side time ⟨inside.1.le, le_rfl⟩
  have actual := (dynamics prepared path).2 index time inside
    (fun side => (endpoint side).trans_le (min_le_left _ _))
  refine ⟨actual.1, ?_⟩
  have radial : ∀ current ∈ Icc 0 time,
      |radialShape prepared.trajectory.movingFamily.patchMotion current index| ≤ 1 / 2 := by
    intro current member
    have raw := small 0 current member
    have identity : radialShape prepared.trajectory.movingFamily.patchMotion current index =
        unstableShape prepared.trajectory.movingFamily.patchMotion current index +
          stableShape prepared.trajectory.movingFamily.patchMotion current index := by
      unfold unstableShape stableShape
      ring
    rw [identity]
    exact (abs_add_le _ _).trans (raw.le.trans ((min_le_left _ _).trans (baseSmall.trans (by norm_num))))
  have diagonal := joint prepared path (thresholdSmall.trans (by norm_num)) factorSmall index nonterminal time inside.1.le inside.2.le radial
    time ⟨inside.1.le, le_rfl⟩
  have firstLower : (1 / 2 : ℝ) ≤ diagonalDifference prepared.trajectory.movingFamily.patchMotion time index /
      changed.length (index.val + 1) ^ 2 := by linarith [(abs_le.mp diagonal.1).1]
  obtain ⟨_, _, _, _, _, coarse, _⟩ := prepared.referenceSolution
  have secondLower := (coarse.2.1 time ⟨inside.1.le, by linarith [inside.2, path.stopBound]⟩ index).2.2.1
  have referenceBound := errorBound
    (unstableShape prepared.reference time index, stableShape prepared.reference time index)
    ((endpoint 1).trans_le (min_le_right _ _))
  exact dilation_relative_saddle_remainder_norm_le
    (changed.omega (index.val + 1))
    (diagonalDifference prepared.trajectory.movingFamily.patchMotion time index / changed.length (index.val + 1) ^ 2)
    (diagonalDifference prepared.reference time index / changed.length (index.val + 1) ^ 2)
    (referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time)
    (referenceStraightenedShape prepared.reference graph coordinate index time)
    (localNormalFormError 1 graph coordinate (unstableShape prepared.trajectory.movingFamily.patchMotion time index,
      stableShape prepared.trajectory.movingFamily.patchMotion time index))
    (localNormalFormError 1 graph coordinate (unstableShape prepared.reference time index, stableShape prepared.reference time index))
    constantNonnegative (by linarith) firstLower secondLower actual.2 referenceBound

end EulerNonuniqueness.Paper
