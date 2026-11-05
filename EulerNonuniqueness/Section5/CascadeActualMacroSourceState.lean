import EulerNonuniqueness.Section5.CascadeActualStrongFirstMoment
import EulerNonuniqueness.Section6.MovingQuadrupoleMacroState
import EulerNonuniqueness.Section6.MovingQuadrupoleReceiverComparison

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.CascadeSourcePreparedPair

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

variable {rawCap sourceRadius : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
  {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
  {count : ℕ}

def macroSourceState
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (time : ℝ) (source : Fin count) : ℝ :=
  let first := prepared.referenceWitness.trajectory.movingFamily
  let second := prepared.trajectory.movingFamily
  let firstCenter := quadrupoleCenter first.patchMotion time source
  let secondCenter := quadrupoleCenter second.patchMotion time source
  (‖firstCenter - secondCenter‖ + ∑ patch : Fin 4,
    ‖(first.cascadeCenters time (source, patch) - firstCenter) -
      (second.cascadeCenters time (source, patch) - secondCenter)‖) / scales.location (source.val + 1) +
    ∑ patch : Fin 4,
      let initial := diskPhysicalSpectralCoordinate ((prepared.referenceWitness.trajectory.curve time).2.2 (finProdFinEquiv (source, patch)))
      let final := diskPhysicalSpectralCoordinate ((prepared.trajectory.curve time).2.2 (finProdFinEquiv (source, patch)))
      ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
        (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
          ‖diskNeutralCLM initial - diskNeutralCLM final‖

theorem sourceComparison_relativeMacroState
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (receiver : Fin (count * 4))
    (shapes : ∀ label, ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label)) (source : Fin count) :
    ((prepared.sourceComparison path inside receiver shapes).quadrupole source).relativeMacroState
      (quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source)
      (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source)
      (scales.location (source.val + 1)) = prepared.macroSourceState time source := by
  with_reducible_and_instances
    dsimp only [MovingPatchFamilySourceComparison.relativeMacroState, macroSourceState,
      MovingPatchFamilySourceComparison.quadrupole, FiniteMovingPatchFamily.quadrupoleSubfamily,
      MovingPatchFamilySourceComparison.source, MovingPatchSourceComparison.spectralDifferenceBudget,
      sourceComparison, FiniteMovingPatchFamily.cascadeCenters]

theorem macroSourceState_nonnegative
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (time : ℝ) (source : Fin count) : 0 ≤ prepared.macroSourceState time source := by
  have positive := scales.location_pos (source.val + 1)
  unfold macroSourceState
  positivity

theorem macroSourceState_center_difference
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (time : ℝ) (source : Fin count) :
    ‖quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source -
      quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ ≤
      scales.location (source.val + 1) * prepared.macroSourceState time source := by
  have positive := scales.location_pos (source.val + 1)
  unfold macroSourceState
  rw [mul_add, mul_div_cancel₀ _ positive.ne']
  rw [add_assoc]
  apply le_add_of_nonneg_right
  positivity

end EulerNonuniqueness.Paper.CascadeSourcePreparedPair
