import EulerNonuniqueness.Section5.CascadeMaterialPreparedPair
import EulerNonuniqueness.Section5.CascadeMaterialCenterGeometry

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper.CascadeMaterialPreparedPair

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}

def neutralVelocity
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (index : Fin count) (time : ℝ) : ℂ :=
  ((prepared.trajectory.velocity time).2.1 (finProdFinEquiv (index, 0)) +
    (prepared.trajectory.velocity time).2.1 (finProdFinEquiv (index, 1)) -
    (prepared.trajectory.velocity time).2.1 (finProdFinEquiv (index, 2)) -
    (prepared.trajectory.velocity time).2.1 (finProdFinEquiv (index, 3))) / 4

theorem neutralVelocity_continuous
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (index : Fin count) :
    Continuous (prepared.neutralVelocity index) := by
  have point (patch : Fin 4) : Continuous (fun time =>
      (prepared.trajectory.velocity time).2.1 (finProdFinEquiv (index, patch))) :=
    (continuous_apply _).comp (continuous_fst.comp (continuous_snd.comp prepared.trajectory.velocity_continuous))
  exact (((point 0).add (point 1)).sub (point 2)).sub (point 3) |>.div_const 4

theorem centroidAsymmetry_hasDerivAt_velocity
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (index : Fin count) {time : ℝ} (inside : time ∈ Ioo (-(1 : ℝ)) 3) :
    HasDerivAt (fun current => centroidAsymmetry prepared.trajectory.movingFamily.patchMotion current index)
      (prepared.neutralVelocity index time) time := by
  have point (patch : Fin 4) : HasDerivAt
      (fun current => patchCentroid prepared.trajectory.movingFamily.patchMotion current index patch)
      ((prepared.trajectory.velocity time).2.1 (finProdFinEquiv (index, patch))) time := by
    apply (prepared.trajectory.center_hasDerivAt (finProdFinEquiv (index, patch)) time).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
    change patchCentroid prepared.trajectory.movingFamily.patchMotion current index patch =
      prepared.trajectory.center (finProdFinEquiv (index, patch)) current
    exact (prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) member index patch).symm
  exact ((((point 0).add (point 1)).sub (point 2)).sub (point 3)).div_const 4

end EulerNonuniqueness.Paper.CascadeMaterialPreparedPair
