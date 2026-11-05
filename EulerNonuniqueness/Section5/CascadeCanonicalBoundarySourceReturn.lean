import EulerNonuniqueness.Section5.CascadeOwnBoundarySourceReturn
import EulerNonuniqueness.Section5.CascadeActualPatchMacroCoefficientSeriesAction
import EulerNonuniqueness.Section5.CascadeCanonicalOwnForeignSeries
import EulerNonuniqueness.Section5.CascadeSourceCapMonotonicity

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_canonical_boundary_source_return :
    ∃ rawCap > (0 : ℝ), ∃ foreignConstant ≥ (0 : ℝ),
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
    let centerState := ‖(fun patch => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver.1 patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver.1) -
      (fun patch => patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver.1 patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time receiver.1)‖ / changed.length (receiver.1.val + 1)
    let ownShapeState := ∑ patch ∈ Finset.univ.erase receiver.2,
      let initial := diskPhysicalSpectralCoordinate ((prepared.referenceWitness.trajectory.curve time).2.2 (finProdFinEquiv (receiver.1, patch)))
      let final := diskPhysicalSpectralCoordinate ((prepared.trajectory.curve time).2.2 (finProdFinEquiv (receiver.1, patch)))
      ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
        (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
          ‖diskNeutralCLM initial - diskNeutralCLM final‖
    Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorStaticCoefficient (finProdFinEquiv receiver) time power -
        prepared.trajectory.movingFamily.canonicalExteriorStaticCoefficient (finProdFinEquiv receiver) time power‖) ∧
    FiniteMovingPatchFamily.canonicalExteriorCoefficientPairSeries
        prepared.referenceWitness.trajectory.movingFamily prepared.trajectory.movingFamily
        (finProdFinEquiv receiver) (finProdFinEquiv receiver) time ≤
      ownConstant * changed.omega (receiver.1.val + 1) *
        (centerState + (changed.radius (receiver.1.val + 1) ^ 2 / changed.length (receiver.1.val + 1) ^ 2) * ownShapeState) +
      (foreignConstant / changed.location (receiver.1.val + 1) ^ 4) *
        (216360000 * changed.hessian + 576 * changed.strain) *
          ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖ := by
  obtain ⟨ownRadius, ownRadiusPositive, ownCap, ownCapPositive, ownFactory⟩ :=
    exists_uniform_actual_own_boundary_source_return
  obtain ⟨foreignRadius, foreignRadiusPositive, foreignCap, foreignCapPositive,
    foreignBaseConstant, foreignBaseNonnegative, foreignFactory⟩ :=
    exists_uniform_actual_patch_macro_coefficient_series_action
  refine ⟨min ownCap foreignCap, lt_min ownCapPositive foreignCapPositive,
    1000000000 * (foreignBaseConstant + 1) * 96, by positivity, ?_⟩
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
  let ownPrepared := prepared.enlargeCap (min_le_left ownCap foreignCap)
  let foreignPrepared := prepared.enlargeCap (min_le_right ownCap foreignCap)
  obtain ⟨ownShapes, ownActual⟩ := ownEstimate count orbit sectionTime phase dipoleAngle ownPrepared path inside receiver
  obtain ⟨foreignShapes, firstCenterIdentity, secondCenterIdentity, radiusIdentity, foreignSummable, foreignActual⟩ :=
    foreignEstimate count phase dipoleAngle foreignPrepared path inside receiver
  let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) foreignShapes
  have budgetIdentity :
      (∑ patch ∈ Finset.univ.erase receiver.2,
        (((ownPrepared.sourceComparison path inside (finProdFinEquiv receiver) ownShapes).quadrupole receiver.1).source patch).spectralDifferenceBudget) =
      ∑ patch ∈ Finset.univ.erase receiver.2,
        let initial := diskPhysicalSpectralCoordinate ((prepared.referenceWitness.trajectory.curve time).2.2 (finProdFinEquiv (receiver.1, patch)))
        let final := diskPhysicalSpectralCoordinate ((prepared.trajectory.curve time).2.2 (finProdFinEquiv (receiver.1, patch)))
        ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
            ‖diskNeutralCLM initial - diskNeutralCLM final‖ := by
    apply Finset.sum_congr rfl
    intro patch member
    with_reducible_and_instances
      dsimp only [MovingPatchSourceComparison.spectralDifferenceBudget,
        MovingPatchFamilySourceComparison.source, MovingPatchFamilySourceComparison.quadrupole,
        CascadeSourcePreparedPair.sourceComparison, ownPrepared, CascadeSourcePreparedPair.enlargeCap]
  have ownRaw := ownActual.2
  rw [budgetIdentity] at ownRaw
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
  have macroStateIdentity (source : Fin count) :
      foreignPrepared.macroSourceState time source = prepared.macroSourceState time source := by
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.macroSourceState, foreignPrepared, CascadeSourcePreparedPair.enlargeCap]
  have macroArrayIdentity :
      (fun source : Fin count => changed.location (source.val + 1) ^ 4 * foreignPrepared.macroSourceState time source) =
      (fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source) := by
    funext source
    rw [macroStateIdentity]
  rw [macroArrayIdentity] at foreignActual
  have split := prepared.canonicalExteriorCoefficientPairSeries_le_own_foreign path inside receiver foreignShapes
    ownSummable actualForeignSummable
  refine ⟨split.1, split.2.trans ?_⟩
  apply add_le_add
  · rw [receiverRadiusIdentity]
    exact ownRaw
  · have locationPositive := pow_pos (changed.location_pos (receiver.1.val + 1)) 4
    calc
      _ ≤ ((1000000000 * (foreignBaseConstant + 1) * 96) *
          (216360000 * changed.hessian + 576 * changed.strain) *
          ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖) /
          changed.location (receiver.1.val + 1) ^ 4 :=
        (le_div_iff₀ locationPositive).mpr (by simpa only [mul_comm] using foreignActual)
      _ = _ := by ring

end EulerNonuniqueness.Paper
