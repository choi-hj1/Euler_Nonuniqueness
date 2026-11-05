import EulerNonuniqueness.Section5.CascadeRelativeNeutralHistory

noncomputable section

open Set MeasureTheory Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : MovingContourState (count * 4)}

def quadrupoleCenterVelocity
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (index : Fin count) (time : ℝ) : ℂ :=
  (∑ patch : Fin 4, (trajectory.velocity time).2.1 (finProdFinEquiv (index, patch))) / 4

theorem quadrupoleCenterVelocity_continuous
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (index : Fin count) :
    Continuous (trajectory.quadrupoleCenterVelocity index) := by
  have point (patch : Fin 4) : Continuous (fun time =>
      (trajectory.velocity time).2.1 (finProdFinEquiv (index, patch))) :=
    (continuous_apply _).comp (continuous_fst.comp (continuous_snd.comp trajectory.velocity_continuous))
  exact (continuous_finset_sum Finset.univ (fun patch _ => point patch)).div_const 4

theorem quadrupoleCenter_hasDerivAt_quadrupoleCenterVelocity
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    (index : Fin count) {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) :
    HasDerivAt (fun current => quadrupoleCenter trajectory.movingFamily.patchMotion current index)
      (trajectory.quadrupoleCenterVelocity index time) time := by
  have point (patch : Fin 4) : HasDerivAt
      (fun current => patchCentroid trajectory.movingFamily.patchMotion current index patch)
      ((trajectory.velocity time).2.1 (finProdFinEquiv (index, patch))) time := by
    apply (trajectory.center_hasDerivAt (finProdFinEquiv (index, patch)) time).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
    exact (trajectory.cascadeCenters_eq_patchCentroid initialCircles member index patch).symm
  exact (HasDerivAt.sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => point patch)).div_const 4

end MovingCentroidGaugeTrajectory

namespace CascadeMaterialPreparedPair

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}

def pairedCenterVelocity
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (side : Fin 2) : Fin count → ℝ → ℂ :=
  Fin.cases prepared.trajectory.quadrupoleCenterVelocity
    (fun _ => prepared.referenceWitness.trajectory.quadrupoleCenterVelocity) side

theorem pairedCenterVelocity_continuous
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (side : Fin 2) (index : Fin count) :
    Continuous (prepared.pairedCenterVelocity side index) := by
  fin_cases side <;> exact MovingCentroidGaugeTrajectory.quadrupoleCenterVelocity_continuous _ index

theorem paired_center_hasDerivAt
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (side : Fin 2) (index : Fin count)
    {time : ℝ} (inside : time ∈ Ioo (-(1 : ℝ)) 3) :
    HasDerivAt (fun current => quadrupoleCenter (cascadePairedMotion prepared side) current index)
      (prepared.pairedCenterVelocity side index time) time := by
  fin_cases side
  · exact prepared.trajectory.quadrupoleCenter_hasDerivAt_quadrupoleCenterVelocity (fun _ => rfl) index inside
  · simpa only [cascadePairedMotion, pairedCenterVelocity, Fin.cases_succ, prepared.referenceIdentity] using
      prepared.referenceWitness.trajectory.quadrupoleCenter_hasDerivAt_quadrupoleCenterVelocity
        (fun _ => rfl) index inside

end CascadeMaterialPreparedPair

theorem CascadeInternallyStoppedPath.relative_center_original_history
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared) (index : Fin count) (nonterminal : index.val + 1 < count)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) :
    quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index - quadrupoleCenter prepared.reference time index =
      ∫ current in (0 : ℝ)..time, prepared.pairedCenterVelocity 0 index current - prepared.pairedCenterVelocity 1 index current := by
  have continuous := (prepared.pairedCenterVelocity_continuous 0 index).sub
    (prepared.pairedCenterVelocity_continuous 1 index)
  have derivative (current : ℝ) (member : current ∈ Icc 0 time) :=
    (prepared.paired_center_hasDerivAt 0 index
      (show current ∈ Ioo (-(1 : ℝ)) 3 from ⟨by linarith [member.1], by linarith [member.2, inside.2, path.stopBound]⟩)).sub
    (prepared.paired_center_hasDerivAt 1 index
      (show current ∈ Ioo (-(1 : ℝ)) 3 from ⟨by linarith [member.1], by linarith [member.2, inside.2, path.stopBound]⟩))
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1
    (fun current member => (derivative current member).continuousAt.continuousWithinAt)
    (fun current member => derivative current ⟨member.1.le, member.2.le⟩)
    (continuous.intervalIntegrable 0 time)
  change (∫ current in (0 : ℝ)..time, prepared.pairedCenterVelocity 0 index current - prepared.pairedCenterVelocity 1 index current) =
    quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index - quadrupoleCenter prepared.reference time index -
      (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion 0 index - quadrupoleCenter prepared.reference 0 index) at identity
  rw [prepared.nonterminal_initial_center index nonterminal, sub_self, sub_zero] at identity
  exact identity.symm

end EulerNonuniqueness.Paper
