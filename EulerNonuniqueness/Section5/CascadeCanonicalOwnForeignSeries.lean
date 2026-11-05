import EulerNonuniqueness.Section5.CascadeActualSourceComparison
import EulerNonuniqueness.Section6.MovingErasedOwnForeignSeries
import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundaryHistory

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.CascadeSourcePreparedPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

variable {rawCap sourceRadius : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
  {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
  {count : ℕ}

theorem canonicalExteriorCoefficientPairSeries_le_own_foreign
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (receiver : Fin count × Fin 4)
    (shapes : ∀ label, ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label)) :
    let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
    Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖(comparison.quadrupole receiver.1).first.exteriorTaylorCoefficient (Finset.univ.erase receiver.2)
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        (comparison.quadrupole receiver.1).second.exteriorTaylorCoefficient (Finset.univ.erase receiver.2)
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) →
    Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) →
    Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorStaticCoefficient (finProdFinEquiv receiver) time power -
        prepared.trajectory.movingFamily.canonicalExteriorStaticCoefficient (finProdFinEquiv receiver) time power‖) ∧
    FiniteMovingPatchFamily.canonicalExteriorCoefficientPairSeries
        prepared.referenceWitness.trajectory.movingFamily prepared.trajectory.movingFamily
        (finProdFinEquiv receiver) (finProdFinEquiv receiver) time ≤
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖(comparison.quadrupole receiver.1).first.exteriorTaylorCoefficient (Finset.univ.erase receiver.2)
            comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          (comparison.quadrupole receiver.1).second.exteriorTaylorCoefficient (Finset.univ.erase receiver.2)
            comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) +
      ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖ := by
  intro comparison ownSummable foreignSummable
  have actual := comparison.exteriorTaylorCoefficient_erased_weighted_difference_le_own_foreign
    receiver (weight := 96) (by norm_num) ownSummable foreignSummable
  have radiusEqual :
      (prepared.referenceWitness.trajectory.movingFamily.patch (finProdFinEquiv receiver)).radius =
        (prepared.trajectory.movingFamily.patch (finProdFinEquiv receiver)).radius :=
    (prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes).radiusEqual (finProdFinEquiv receiver)
  simpa only [FiniteMovingPatchFamily.canonicalExteriorCoefficientPairSeries,
    FiniteMovingPatchFamily.canonicalExteriorStaticCoefficient, ← radiusEqual] using actual

end EulerNonuniqueness.Paper.CascadeSourcePreparedPair
