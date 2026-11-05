import EulerNonuniqueness.Section5.CascadeStoppedMaterialGeometry
import EulerNonuniqueness.Section3.MovingMaterialCentroidRegularity

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.CascadeInternallyStoppedPath

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count}

theorem halfDiagonal_continuousOn (path : CascadeInternallyStoppedPath prepared) (index : Fin count) :
    ContinuousOn (fun time => positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index)
        (Icc 0 path.stop) ∧
      ContinuousOn (fun time => negativeHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index)
        (Icc 0 path.stop) := by
  have centroids (patch : Fin 4) : ContinuousOn
      (fun time => patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch) (Icc 0 path.stop) := by
    simp_rw [FiniteMovingPatchFamily.patchCentroid_eq]
    intro time inside
    apply ((prepared.trajectory.movingFamily.patch _).centroid_contDiffAt ?_).continuousAt.continuousWithinAt
    change time ∈ Ioo (-(1 : ℝ)) 3
    exact ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  exact ⟨((centroids 0).sub (centroids 1)).div_const 2,
    ((centroids 2).sub (centroids 3)).div_const 2⟩

theorem halfDiagonal_norm_lower (path : CascadeInternallyStoppedPath prepared)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (index : Fin count) :
    factor * scales.length (index.val + 1) / 2 ≤
        ‖positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index‖ ∧
      factor * scales.length (index.val + 1) / 2 ≤
        ‖negativeHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index‖ := by
  have first := path.internal_centroid_gap inside index 0 1 (by decide)
  have second := path.internal_centroid_gap inside index 2 3 (by decide)
  constructor
  · dsimp only [positiveHalfDiagonal]
    rw [norm_div, Complex.norm_ofNat]
    exact div_le_div_of_nonneg_right first (by norm_num)
  · dsimp only [negativeHalfDiagonal]
    rw [norm_div, Complex.norm_ofNat]
    exact div_le_div_of_nonneg_right second (by norm_num)

theorem radialShape_continuousOn (path : CascadeInternallyStoppedPath prepared)
    (factorPositive : 0 < factor) (index : Fin count) :
    ContinuousOn (fun time => radialShape prepared.trajectory.movingFamily.patchMotion time index)
      (Icc 0 path.stop) := by
  obtain ⟨positive, negative⟩ := path.halfDiagonal_continuousOn index
  have nonzero (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      ‖positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index‖ ^ 2 ≠ 0 := by
    have lower := (path.halfDiagonal_norm_lower inside index).1
    have positiveNorm := (div_pos (mul_pos factorPositive (scales.length_pos _)) (by norm_num : (0 : ℝ) < 2)).trans_le lower
    exact (sq_pos_of_pos positiveNorm).ne'
  exact (((negative.norm.pow 2).div (positive.norm.pow 2) nonzero).sub continuousOn_const).div_const rhombusRatio

end EulerNonuniqueness.Paper.CascadeInternallyStoppedPath
