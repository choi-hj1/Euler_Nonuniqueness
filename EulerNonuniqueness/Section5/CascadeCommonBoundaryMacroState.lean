import EulerNonuniqueness.Section5.CascadeActualCommonBoundaryJointSource
import EulerNonuniqueness.Section5.CascadeActualMacroSourceState

noncomputable section

open Set Filter MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

open EulerNonuniqueness.General EulerNonuniqueness.Section6 FiniteMovingPatchFamily

theorem exists_uniform_actual_common_boundary_macro_state :
    ∃ rawCap > 0, ∀ factor : ℝ, 0 < factor → factor ≤ 1 →
    ∃ constant ≥ (1 : ℝ), ∃ radiusCoefficient ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant : ℝ, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {requestedCap shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeSourcePreparedPair requestedCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      0 < requestedCap → requestedCap ≤ rawCap →
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ (source : Fin count), ∀ time ∈ Icc 0 path.stop,
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
      let final := prepared.trajectory.movingFamily.patchMotion
      let centerState := ‖(fun patch => patchCentroid first time source patch - quadrupoleCenter first time source) -
        (fun patch => patchCentroid final time source patch - quadrupoleCenter final time source)‖ / changed.length (source.val + 1)
      let radius := radiusCoefficient / (scaleRoot ^ 2 * changed.omega (source.val + 1) ^ 2)
      let boundary := fun patch current => prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonBoundaryDistance
        (finProdFinEquiv (source, patch)) (patchSign patch * changed.amplitude * changed.omega (source.val + 1) ^ 4) current radius
        (prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) current)
        (prepared.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) current)
      prepared.macroSourceState time source ≤
        ‖quadrupoleCenter first time source - quadrupoleCenter final time source‖ / changed.location (source.val + 1) +
          4 * (changed.length (source.val + 1) / changed.location (source.val + 1)) * centerState +
          constant * (∑ patch : Fin 4, boundary patch time) ∧
      ∀ patch : Fin 4,
        |patchSign patch * changed.amplitude * changed.omega (source.val + 1) ^ 4| * radius ^ 2 ≤ 1 ∧
        boundary patch time ≤ ∫ current in (0 : ℝ)..time, constant * canonicalExteriorCoefficientPairSeries
          prepared.referenceWitness.trajectory.movingFamily prepared.trajectory.movingFamily
          (finProdFinEquiv (source, patch)) (finProdFinEquiv (source, patch)) current := by
  obtain ⟨rawCap, rawPositive, parameters⟩ := exists_uniform_actual_common_boundary_joint_source_history
  refine ⟨rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨constant, constantOne, coefficient, coefficientOne, rootMin, rootEight, bounds⟩ := parameters factor factorPositive factorSmall
  refine ⟨constant, constantOne, coefficient, coefficientOne, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative
  filter_upwards [bounds scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive
    threshold referenceConstant thresholdSmall referenceNonnegative] with frequency actual
  intro count orbit sectionTime phase dipoleAngle requestedCap shapeRadius monitor boundaryConstant prepared requestedPositive requestedSmall path source time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let firstFamily := prepared.referenceWitness.trajectory.movingFamily
  let finalFamily := prepared.trajectory.movingFamily
  let first := firstFamily.patchMotion
  let final := finalFamily.patchMotion
  let firstCenter := quadrupoleCenter first time source
  let finalCenter := quadrupoleCenter final time source
  let centered := (fun patch => patchCentroid first time source patch - firstCenter) -
    (fun patch => patchCentroid final time source patch - finalCenter)
  let radius := coefficient / (scaleRoot ^ 2 * changed.omega (source.val + 1) ^ 2)
  let boundary := fun patch current => firstFamily.canonicalExteriorCommonBoundaryDistance
    (finProdFinEquiv (source, patch)) (patchSign patch * changed.amplitude * changed.omega (source.val + 1) ^ 4) current radius
    (prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) current)
    (prepared.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) current)
  let rawBudget := fun patch : Fin 4 =>
    let initial := prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) time
    let finalState := prepared.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) time
    ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection finalState‖ +
      (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection finalState‖) *
        ‖diskNeutralCLM initial - diskNeutralCLM finalState‖
  have pointwise (patch : Fin 4) := actual count orbit sectionTime phase dipoleAngle prepared requestedPositive requestedSmall path source patch time inside
  have rawBound (patch : Fin 4) : rawBudget patch ≤ constant * boundary patch time := by
    with_reducible_and_instances
      exact (pointwise patch).1
  have sumBound : (∑ patch : Fin 4, rawBudget patch) ≤ constant * ∑ patch : Fin 4, boundary patch time := by
    calc
      _ ≤ ∑ patch : Fin 4, constant * boundary patch time := Finset.sum_le_sum (fun patch _ => rawBound patch)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have positionSum : (∑ patch : Fin 4,
      ‖(firstFamily.cascadeCenters time (source, patch) - firstCenter) -
        (finalFamily.cascadeCenters time (source, patch) - finalCenter)‖) ≤ 4 * ‖centered‖ := by
    dsimp only [firstFamily, finalFamily]
    simp_rw [prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside,
      prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside]
    exact quadrupoleCenteredPositionDifference_sum_le_array_norm first final source time
  have locationPositive := changed.location_pos (source.val + 1)
  have lengthPositive := changed.length_pos (source.val + 1)
  have positionBound := div_le_div_of_nonneg_right positionSum locationPositive.le
  have scaleIdentity : (4 * ‖centered‖) / changed.location (source.val + 1) =
      4 * (changed.length (source.val + 1) / changed.location (source.val + 1)) *
        (‖centered‖ / changed.length (source.val + 1)) := by
    field_simp [lengthPositive.ne', locationPositive.ne']
    <;> ring
  have identity : prepared.macroSourceState time source =
      ‖firstCenter - finalCenter‖ / changed.location (source.val + 1) +
        (∑ patch : Fin 4, ‖(firstFamily.cascadeCenters time (source, patch) - firstCenter) -
          (finalFamily.cascadeCenters time (source, patch) - finalCenter)‖) / changed.location (source.val + 1) +
        ∑ patch : Fin 4, rawBudget patch := by
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.macroSourceState, rawBudget, firstCenter, finalCenter,
        first, final, firstFamily, finalFamily, MovingCentroidGaugeTrajectory.spectralCoordinate]
      rw [add_div]
  have macroBound := identity.le.trans (add_le_add
    (add_le_add_left positionBound (‖firstCenter - finalCenter‖ / changed.location (source.val + 1))) sumBound)
  rw [scaleIdentity] at macroBound
  constructor
  · with_reducible_and_instances
      simpa only [firstCenter, finalCenter, centered, first, final, firstFamily, finalFamily, boundary, radius, changed] using macroBound
  · intro patch
    with_reducible_and_instances
      exact (pointwise patch).2

end EulerNonuniqueness.Paper
