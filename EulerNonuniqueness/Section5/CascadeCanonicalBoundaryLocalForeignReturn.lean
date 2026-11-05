import EulerNonuniqueness.Section5.CascadeOwnBoundarySourceReturn
import EulerNonuniqueness.Section5.CascadeActualPatchMacroCoefficientSeriesAction
import EulerNonuniqueness.Section5.CascadeCanonicalOwnForeignSeries
import EulerNonuniqueness.Section5.CascadeRawSourceWeightedFeedback
import EulerNonuniqueness.Section5.CascadeSourceCapMonotonicity

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_canonical_boundary_local_foreign_return :
    ∃ rawCap > (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 → ∃ ownConstant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ {time : ℝ}, time ∈ Icc 0 path.stop → ∀ receiver : Fin count × Fin 4,
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.referenceWitness.trajectory.movingFamily
    let second := prepared.trajectory.movingFamily
    let foreign := fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          (fun current => patchCentroid first.patchMotion current receiver.1 receiver.2)
          (changed.radius (receiver.1.val + 1)) (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          (fun current => patchCentroid second.patchMotion current receiver.1 receiver.2)
          (changed.radius (receiver.1.val + 1)) (power + 1) time‖
    Summable foreign ∧
    Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖first.canonicalExteriorStaticCoefficient (finProdFinEquiv receiver) time power -
        second.canonicalExteriorStaticCoefficient (finProdFinEquiv receiver) time power‖) ∧
    FiniteMovingPatchFamily.canonicalExteriorCoefficientPairSeries first second
        (finProdFinEquiv receiver) (finProdFinEquiv receiver) time ≤
      ownConstant * changed.omega (receiver.1.val + 1) *
        (prepared.rawSourceCenteredState time receiver.1 +
          (changed.radius (receiver.1.val + 1) ^ 2 / changed.length (receiver.1.val + 1) ^ 2) *
            ∑ patch ∈ Finset.univ.erase receiver.2, prepared.rawSourceShapeBudget time receiver.1 patch) +
        ∑' power : ℕ, foreign power := by
  obtain ⟨ownRadius, ownRadiusPositive, ownCap, ownCapPositive, ownFactory⟩ :=
    exists_uniform_actual_own_boundary_source_return
  obtain ⟨foreignRadius, foreignRadiusPositive, foreignCap, foreignCapPositive,
    foreignBaseConstant, foreignBaseNonnegative, foreignFactory⟩ :=
    exists_uniform_actual_patch_macro_coefficient_series_action
  refine ⟨min ownCap foreignCap, lt_min ownCapPositive foreignCapPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨ownConstant, ownNonnegative, ownBound⟩ := ownFactory factorPositive factorSmall
  refine ⟨ownConstant, ownNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne
  filter_upwards [ownBound scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    foreignFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorSmall] with frequency ownEstimate foreignEstimate
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily
  let second := prepared.trajectory.movingFamily
  let foreign := fun power : ℕ => (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
        (fun current => patchCentroid first.patchMotion current receiver.1 receiver.2)
        (changed.radius (receiver.1.val + 1)) (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
        (fun current => patchCentroid second.patchMotion current receiver.1 receiver.2)
        (changed.radius (receiver.1.val + 1)) (power + 1) time‖
  let ownPrepared := prepared.enlargeCap (min_le_left ownCap foreignCap)
  let foreignPrepared := prepared.enlargeCap (min_le_right ownCap foreignCap)
  obtain ⟨ownShapes, ownActual⟩ := ownEstimate count orbit sectionTime phase dipoleAngle ownPrepared path inside receiver
  obtain ⟨foreignShapes, _, _, radiusIdentity, foreignSummable, _⟩ :=
    foreignEstimate count phase dipoleAngle foreignPrepared path inside receiver
  let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) foreignShapes
  have budgetIdentity :
      (∑ patch ∈ Finset.univ.erase receiver.2,
        (((ownPrepared.sourceComparison path inside (finProdFinEquiv receiver) ownShapes).quadrupole receiver.1).source patch).spectralDifferenceBudget) =
      ∑ patch ∈ Finset.univ.erase receiver.2, prepared.rawSourceShapeBudget time receiver.1 patch := by
    apply Finset.sum_congr rfl
    intro patch member
    with_reducible_and_instances
      dsimp only [MovingPatchSourceComparison.spectralDifferenceBudget, CascadeSourcePreparedPair.rawSourceShapeBudget,
        MovingCentroidGaugeTrajectory.spectralCoordinate, MovingPatchFamilySourceComparison.source,
        MovingPatchFamilySourceComparison.quadrupole, CascadeSourcePreparedPair.sourceComparison,
        ownPrepared, CascadeSourcePreparedPair.enlargeCap]
  have centerIdentity :
      ‖(fun patch => patchCentroid ownPrepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver.1 patch -
          quadrupoleCenter ownPrepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver.1) -
        (fun patch => patchCentroid ownPrepared.trajectory.movingFamily.patchMotion time receiver.1 patch -
          quadrupoleCenter ownPrepared.trajectory.movingFamily.patchMotion time receiver.1)‖ /
          changed.length (receiver.1.val + 1) = prepared.rawSourceCenteredState time receiver.1 := by
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.rawSourceCenteredState, ownPrepared, CascadeSourcePreparedPair.enlargeCap]
  have ownRaw := ownActual.2
  rw [budgetIdentity, centerIdentity] at ownRaw
  have receiverRadiusIdentity : comparison.receiverRadius = changed.radius (receiver.1.val + 1) := radiusIdentity
  have ownSummable : Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖(comparison.quadrupole receiver.1).first.exteriorTaylorCoefficient (Finset.univ.erase receiver.2)
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        (comparison.quadrupole receiver.1).second.exteriorTaylorCoefficient (Finset.univ.erase receiver.2)
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) := by
    rw [receiverRadiusIdentity]
    exact ownActual.1
  have actualForeignSummable : Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) := foreignSummable
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have firstReceiverIdentity : comparison.firstReceiver time = patchCentroid first.patchMotion time receiver.1 receiver.2 :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver.1 receiver.2
  have secondReceiverIdentity : comparison.secondReceiver time = patchCentroid second.patchMotion time receiver.1 receiver.2 :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver.1 receiver.2
  have foreignIdentity : (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) = foreign := by
    funext power
    rw [receiverRadiusIdentity]
    change (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.firstReceiver (changed.radius (receiver.1.val + 1)) (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.secondReceiver (changed.radius (receiver.1.val + 1)) (power + 1) time‖ = _
    dsimp only [foreign, FiniteMovingPatchFamily.exteriorTaylorCoefficient]
    rw [firstReceiverIdentity, secondReceiverIdentity]
  have split := prepared.canonicalExteriorCoefficientPairSeries_le_own_foreign path inside receiver foreignShapes
    ownSummable actualForeignSummable
  refine ⟨?_, split.1, split.2.trans ?_⟩
  · rw [foreignIdentity] at actualForeignSummable
    exact actualForeignSummable
  · apply add_le_add
    · rw [receiverRadiusIdentity]
      exact ownRaw
    · rw [foreignIdentity]

end EulerNonuniqueness.Paper

