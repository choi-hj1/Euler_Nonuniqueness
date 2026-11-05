import EulerNonuniqueness.Section5.CascadeStoppedMaterialGeometry
import EulerNonuniqueness.Section6.MovingBlockCenteredPointEquation

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.CascadeInternallyStoppedPath

open EulerNonuniqueness.Section6

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count}

theorem centeredCentroid_point_equation (path : CascadeInternallyStoppedPath prepared)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (index : Fin count) :
    HasDerivAt (fun current => fourPointCenterProjection
      (fun patch => patchCentroid prepared.trajectory.movingFamily.patchMotion current index patch))
      (fourPointCenteredField (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fourPointCenterProjection
            (fun patch => patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch)) +
        quadrupoleCenteredForcing scales prepared.trajectory.movingFamily.patchMotion time index) time := by
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  exact prepared.trajectory.movingFamily.centeredCentroid_hasDerivAt_point_field path.evolution inside index
    (fun _ => globalInside) (fun patch label => path.material_boundary inside (finProdFinEquiv (index, patch)) label)

end EulerNonuniqueness.Paper.CascadeInternallyStoppedPath
