import EulerNonuniqueness.Section5.CascadeStoppedRadialContinuity
import EulerNonuniqueness.Section4.PaperCoarseUpperBranch

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.CascadeInternallyStoppedPath

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count}

/-- On the actual small-shape branch, the paper coordinates have genuine time continuity. -/
theorem shape_continuousOn_of_small (path : CascadeInternallyStoppedPath prepared)
    (factorPositive : 0 < factor) (index : Fin count) {finish : ℝ} (finishInside : finish ∈ Icc 0 path.stop)
    (small : ∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 4) :
    ContinuousOn (fun time => unstableShape prepared.trajectory.movingFamily.patchMotion time index) (Icc 0 finish) ∧
      ContinuousOn (fun time => stableShape prepared.trajectory.movingFamily.patchMotion time index) (Icc 0 finish) := by
  let motion := prepared.trajectory.movingFamily.patchMotion
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishInside.2
  obtain ⟨positiveContinuous, negativeContinuous⟩ := path.halfDiagonal_continuousOn index
  have nonzero (time : ℝ) (inside : time ∈ Icc 0 finish) : positiveHalfDiagonal motion time index ≠ 0 := by
    have lower := (path.halfDiagonal_norm_lower (subset inside) index).1
    have normPositive :=
      (div_pos (mul_pos factorPositive (scales.length_pos _)) (by norm_num : (0 : ℝ) < 2)).trans_le lower
    exact norm_pos_iff.mp normPositive
  have quotientContinuous := (negativeContinuous.mono subset).div (positiveContinuous.mono subset) nonzero
  have argumentContinuous : ContinuousOn
      (fun time => Complex.arg (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index)) (Icc 0 finish) := by
    intro time inside
    have upper := paper_shape_ratio_im_pos_of_small motion time index (small time inside)
    have argumentAt : ContinuousAt Complex.arg
        (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index) :=
      Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr (Or.inr upper.ne'))
    have quotientAt : ContinuousWithinAt
        (fun current : ℝ => negativeHalfDiagonal motion current index / positiveHalfDiagonal motion current index)
        (Icc 0 finish) time := quotientContinuous time inside
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun current : ℝ => negativeHalfDiagonal motion current index / positiveHalfDiagonal motion current index)
      (s := Icc 0 finish) (x := time) argumentAt quotientAt
  have angularContinuous : ContinuousOn (fun time => angularShape motion time index) (Icc 0 finish) :=
    ((continuousOn_const.mul argumentContinuous).sub continuousOn_const).div_const (Real.sqrt 2)
  have radialContinuous := (path.radialShape_continuousOn factorPositive index).mono subset
  exact ⟨(radialContinuous.add angularContinuous).div_const 2,
    (radialContinuous.sub angularContinuous).div_const 2⟩

end EulerNonuniqueness.Paper.CascadeInternallyStoppedPath
