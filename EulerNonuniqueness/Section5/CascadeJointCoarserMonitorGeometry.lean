import EulerNonuniqueness.Section5.CascadeRegularizedShapePrefixGeometry
import EulerNonuniqueness.Section5.CascadeStoppedRadialContinuity
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect

noncomputable section
open Set Filter
open scoped Topology
namespace EulerNonuniqueness.Paper
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- The dummy label keeps the monitor family inhabited even for the first receiver. -/
def jointCoarserMonitor {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (drive : Fin count) (radius : ℝ)
    (label : Option ({index : Fin count // index.val < drive.val} × Fin 2)) (time : ℝ) : ℝ :=
  match label with
  | none => -1
  | some (index, side) => if side = 0 then |radialShape motion time index.val| - 1 / 2 else
      |(regularizedShapeCoordinates (scales.length (index.val.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal motion time index.val) (negativeHalfDiagonal motion time index.val)).1| +
      |(regularizedShapeCoordinates (scales.length (index.val.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal motion time index.val) (negativeHalfDiagonal motion time index.val)).2| - radius

theorem Scales.eventually_actual_joint_coarser_monitor_geometry (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {scaleRoot boundaryConstant referenceConstant radius : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (referenceNonnegative : 0 ≤ referenceConstant) (radiusPositive : 0 < radius)
    (radiusQuarter : radius ≤ 1 / 4) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold shapeRadius factor monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, 0 < factor → factor ≤ 1 / 8 → threshold ≤ 1 / 2 →
    ∀ drive : Fin count,
    let observed := jointCoarserMonitor {scales with frequency := frequency}
      prepared.trajectory.movingFamily.patchMotion drive radius
    (∀ label, ContinuousOn (observed label) (Icc 0 path.stop)) ∧
    (∀ label, observed label 0 < 0) ∧
    ∀ finish ∈ Icc 0 path.stop,
      (∀ time ∈ Icc 0 finish, ∀ label, observed label time ≤ 0) →
      ∀ index : Fin count, index.val < drive.val → ∀ time ∈ Icc 0 finish,
        |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
          |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius := by
  filter_upwards [scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive
      referenceNonnegative (by positivity : 0 < radius / 8),
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative] with frequency referenceSmall joint
  intro orbit sectionTime phase dipoleAngle threshold shapeRadius factor monitor count prepared path
    factorPositive factorSmall thresholdSmall drive
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  have geometry (index : Fin count) (earlier : index.val < drive.val) := by
    have nonterminal : index.val + 1 < count := by omega
    have reference := referenceSmall prepared 0 (by norm_num) index
    have shapeSmall : |unstableShape prepared.reference 0 index| +
        |stableShape prepared.reference 0 index| < radius / 8 := by
      linarith only [reference, abs_nonneg (diagonalDifference prepared.reference 0 index / changed.length (index.val + 1) ^ 2 - 1)]
    have first : positiveHalfDiagonal motion 0 index = positiveHalfDiagonal prepared.reference 0 index := by
      simp only [motion, positiveHalfDiagonal, prepared.nonterminal_initial_centroid index nonterminal]
    have second : negativeHalfDiagonal motion 0 index = negativeHalfDiagonal prepared.reference 0 index := by
      simp only [motion, negativeHalfDiagonal, prepared.nonterminal_initial_centroid index nonterminal]
    have floor : changed.length (index.val + 1) ^ 2 / 2 ≤ ‖positiveHalfDiagonal motion 0 index‖ ^ 2 := by
      have lower := (abs_lt.mp (show |diagonalDifference prepared.reference 0 index /
        changed.length (index.val + 1) ^ 2 - 1| < radius / 8 by
          linarith only [reference, abs_nonneg (unstableShape prepared.reference 0 index), abs_nonneg (stableShape prepared.reference 0 index)])).1
      have ratio : (1 / 2 : ℝ) ≤ diagonalDifference prepared.reference 0 index / changed.length (index.val + 1) ^ 2 := by linarith
      have product := (le_div_iff₀ (sq_pos_of_pos (changed.length_pos _))).mp ratio
      rw [first]
      dsimp only [diagonalDifference] at product
      nlinarith only [product, sq_nonneg ‖negativeHalfDiagonal prepared.reference 0 index‖]
    exact actual_initial_regularized_geometry prepared index nonterminal radiusPositive radiusQuarter floor shapeSmall
  refine ⟨?_, ?_, ?_⟩
  · intro label
    cases label with
    | none => exact continuousOn_const
    | some pair =>
      obtain ⟨index, side⟩ := pair
      have data := geometry index.val index.property
      fin_cases side
      · simpa only [jointCoarserMonitor, ↓reduceIte] using
          ((path.radialShape_continuousOn factorPositive index.val).abs.sub continuousOn_const)
      · simpa only [jointCoarserMonitor, ↓reduceIte] using
          ((data.2.2.1.fst.abs.add data.2.2.1.snd.abs).sub continuous_const).continuousOn
  · intro label
    cases label with
    | none => norm_num [jointCoarserMonitor]
    | some pair =>
      obtain ⟨index, side⟩ := pair
      have data := geometry index.val index.property
      fin_cases side
      · have nonterminal : index.val.val + 1 < count := by omega
        have first : unstableShape motion 0 index.val = unstableShape prepared.reference 0 index.val := by
          simp only [motion, unstableShape, radialShape, angularShape, positiveHalfDiagonal, negativeHalfDiagonal,
            prepared.nonterminal_initial_centroid index.val nonterminal]
        have second : stableShape motion 0 index.val = stableShape prepared.reference 0 index.val := by
          simp only [motion, unstableShape, stableShape, radialShape, angularShape, positiveHalfDiagonal, negativeHalfDiagonal,
            prepared.nonterminal_initial_centroid index.val nonterminal]
        have reference := referenceSmall prepared 0 (by norm_num) index.val
        have identity := radialShape_eq_unstable_add_stable motion 0 index.val
        have triangle := abs_add (unstableShape motion 0 index.val) (stableShape motion 0 index.val)
        rw [← identity, first, second] at triangle
        change |radialShape motion 0 index.val| - 1 / 2 < 0
        linarith [abs_nonneg (diagonalDifference prepared.reference 0 index.val / changed.length (index.val.val + 1) ^ 2 - 1)]
      · exact sub_neg.mpr data.2.2.2.2
  · intro finish finishInside weak index earlier time inside
    have data := geometry index earlier
    have radial (current : ℝ) (member : current ∈ Icc 0 finish) : |radialShape motion current index| ≤ 1 / 2 := by
      have bound := weak current member (some (⟨index, earlier⟩, 0))
      change |radialShape motion current index| - 1 / 2 ≤ 0 at bound
      linarith only [bound]
    have diagonal := joint prepared path thresholdSmall factorSmall index (by omega)
      finish finishInside.1 finishInside.2 radial
    have floor (current : ℝ) (member : current ∈ Icc 0 finish) :
        changed.length (index.val + 1) ^ 2 / 2 ≤ ‖positiveHalfDiagonal motion current index‖ ^ 2 := by
      have lower := (abs_le.mp (diagonal current member).1).1
      have ratio : (1 / 2 : ℝ) ≤ diagonalDifference motion current index / changed.length (index.val + 1) ^ 2 := by linarith only [lower]
      have product := (le_div_iff₀ (sq_pos_of_pos (changed.length_pos _))).mp ratio
      dsimp only [diagonalDifference] at product
      nlinarith only [product, sq_nonneg ‖negativeHalfDiagonal motion current index‖]
    have size (current : ℝ) (member : current ∈ Icc 0 finish) :=
      weak current member (some (⟨index, earlier⟩, 1))
    have agreement := regularized_shape_prefix_eq_paper motion index
      (div_pos (sq_pos_of_pos (changed.length_pos _)) (by norm_num))
      (data.1.continuousOn) (data.2.1.continuousOn) floor data.2.2.2.1 (by
        intro current member
        have bound := size current member
        change _ - radius ≤ 0 at bound
        linarith only [bound, radiusQuarter]) time inside
    have bound := size time inside
    change _ - radius ≤ 0 at bound
    rw [agreement] at bound
    exact sub_nonpos.mp bound

end EulerNonuniqueness.Paper
