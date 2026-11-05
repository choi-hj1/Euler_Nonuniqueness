import EulerNonuniqueness.Section5.CascadeActualSourceComparison
import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundaryHistory
import EulerNonuniqueness.Section6.MovingExteriorPairRadiusMonotonicity

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem canonicalExteriorCoefficientPairSeries_le_virtual_radius {firstCount finalCount : ℕ}
    (firstFamily : FiniteMovingPatchFamily firstCount) (finalFamily : FiniteMovingPatchFamily finalCount)
    (firstIndex : Fin firstCount) (finalIndex : Fin finalCount) (time virtualRadius : ℝ)
    (radiusEqual : (firstFamily.patch firstIndex).radius = (finalFamily.patch finalIndex).radius)
    (radiusBound : (firstFamily.patch firstIndex).radius ≤ virtualRadius)
    (summable : Summable (fun degree : ℕ => (96 : ℝ) ^ (degree + 1) *
      ‖firstFamily.exteriorTaylorCoefficient (Finset.univ.erase firstIndex)
          (firstFamily.patch firstIndex).center virtualRadius (degree + 1) time -
        finalFamily.exteriorTaylorCoefficient (Finset.univ.erase finalIndex)
          (finalFamily.patch finalIndex).center virtualRadius (degree + 1) time‖)) :
    Summable (fun degree : ℕ => (96 : ℝ) ^ (degree + 1) *
      ‖firstFamily.canonicalExteriorStaticCoefficient firstIndex time degree -
        finalFamily.canonicalExteriorStaticCoefficient finalIndex time degree‖) ∧
    canonicalExteriorCoefficientPairSeries firstFamily finalFamily firstIndex finalIndex time ≤
      ∑' degree : ℕ, (96 : ℝ) ^ (degree + 1) *
        ‖firstFamily.exteriorTaylorCoefficient (Finset.univ.erase firstIndex)
            (firstFamily.patch firstIndex).center virtualRadius (degree + 1) time -
          finalFamily.exteriorTaylorCoefficient (Finset.univ.erase finalIndex)
            (finalFamily.patch finalIndex).center virtualRadius (degree + 1) time‖ := by
  have actual := firstFamily.exteriorTaylorCoefficient_pair_weighted_series_radius_mono finalFamily
    (Finset.univ.erase firstIndex) (Finset.univ.erase finalIndex)
    (firstFamily.patch firstIndex).center (finalFamily.patch finalIndex).center
    (firstFamily.patch firstIndex).radius_positive.le radiusBound (by norm_num : (0 : ℝ) ≤ 96)
    time summable
  simpa only [canonicalExteriorStaticCoefficient, canonicalExteriorCoefficientPairSeries, ← radiusEqual] using actual

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily

namespace EulerNonuniqueness.Paper.CascadeSourcePreparedPair

variable {rawCap sourceRadius : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
  {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
  {count : ℕ}

theorem sourceComparison_canonical_boundary_series_le_virtual_radius
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (receiver : Fin (count * 4))
    (shapes : ∀ label, ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label))
    (virtualRadius : ℝ)
    (radiusBound : (prepared.sourceComparison path inside receiver shapes).receiverRadius ≤ virtualRadius)
    (summable : Summable (fun degree : ℕ => (96 : ℝ) ^ (degree + 1) *
      ‖(prepared.sourceComparison path inside receiver shapes).first.exteriorTaylorCoefficient
          (Finset.univ.erase receiver) (prepared.sourceComparison path inside receiver shapes).firstReceiver
          virtualRadius (degree + 1) time -
        (prepared.sourceComparison path inside receiver shapes).second.exteriorTaylorCoefficient
          (Finset.univ.erase receiver) (prepared.sourceComparison path inside receiver shapes).secondReceiver
          virtualRadius (degree + 1) time‖)) :
    Summable (fun degree : ℕ => (96 : ℝ) ^ (degree + 1) *
      ‖prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorStaticCoefficient receiver time degree -
        prepared.trajectory.movingFamily.canonicalExteriorStaticCoefficient receiver time degree‖) ∧
    FiniteMovingPatchFamily.canonicalExteriorCoefficientPairSeries
      prepared.referenceWitness.trajectory.movingFamily prepared.trajectory.movingFamily receiver receiver time ≤
      ∑' degree : ℕ, (96 : ℝ) ^ (degree + 1) *
        ‖(prepared.sourceComparison path inside receiver shapes).first.exteriorTaylorCoefficient
            (Finset.univ.erase receiver) (prepared.sourceComparison path inside receiver shapes).firstReceiver
            virtualRadius (degree + 1) time -
          (prepared.sourceComparison path inside receiver shapes).second.exteriorTaylorCoefficient
            (Finset.univ.erase receiver) (prepared.sourceComparison path inside receiver shapes).secondReceiver
            virtualRadius (degree + 1) time‖ := by
  exact prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCoefficientPairSeries_le_virtual_radius
    prepared.trajectory.movingFamily receiver receiver time virtualRadius
    ((prepared.sourceComparison path inside receiver shapes).radiusEqual receiver) radiusBound summable

end EulerNonuniqueness.Paper.CascadeSourcePreparedPair
