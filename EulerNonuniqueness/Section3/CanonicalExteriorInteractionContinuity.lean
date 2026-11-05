import EulerNonuniqueness.Section3.CanonicalExteriorMovingContinuity
import EulerNonuniqueness.Section3.DiskNormalizedInteractionAliases

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] normalizedInteractionContinuityC1Group
  physicalGeneratorC1Space physicalGeneratorC1ContinuousAdd
  physicalGeneratorC1UniformAdd physicalGeneratorC1BoundedSMul
  physicalGeneratorOperatorGroup physicalGeneratorOperatorSpace
  physicalScaledOperatorModule physicalScaledOperatorBoundedSMul

attribute [local instance] normalizedUniformSlopeC1Group
  canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero canonicalForcingNeg canonicalForcingSub

open EulerNonuniqueness.Section6

theorem canonicalNormalizedInteractionCurve_eq {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (angular curve : ℝ → PeriodicC1HolderHalf) (frequency : ℝ) :
    (fun current => family.canonicalNormalizedInteractionCoordinate index (angular current)
      frequency current (curve current)) =
    (fun current => diskPhysicalScaledGroup frequency (-current)
      (diskNormalizedQuadraticObservable (family.canonicalExteriorAffineCoordinate index
        (angular current) frequency current (curve current)))) := rfl

theorem canonicalExteriorAffineCoordinate_exists_uniform_physical_geometric_continuity :
    ∃ radius > 0, ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
      {angular curve : ℝ → PeriodicC1HolderHalf} {frequency time distance : ℝ},
    ‖angular time‖ < radius → ContinuousAt angular time → ContinuousAt curve time →
    (∀ᶠ current in 𝓝 time, ∀ label,
      star ((angular current).val.1 label) = (angular current).val.1 label) →
    frequency ≠ 0 → 0 < distance → 48 * (family.patch index).radius ≤ distance →
    (∀ source ∈ Finset.univ.erase index,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
    (∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center time - (family.patch source).center time‖) →
    ContinuousAt (fun current => family.canonicalExteriorAffineCoordinate index (angular current)
      frequency current (curve current)) time := by
  with_reducible_and_instances
    exact canonicalExteriorAffineCoordinate_exists_uniform_geometric_continuity

theorem canonicalNormalizedInteractionCoordinate_exists_uniform_geometric_continuity :
    ∃ radius > 0, ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
      {angular curve : ℝ → PeriodicC1HolderHalf} {frequency time distance : ℝ},
    ‖angular time‖ < radius → ContinuousAt angular time → ContinuousAt curve time →
    (∀ᶠ current in 𝓝 time, ∀ label,
      star ((angular current).val.1 label) = (angular current).val.1 label) →
    frequency ≠ 0 → 0 < distance → 48 * (family.patch index).radius ≤ distance →
    (∀ source ∈ Finset.univ.erase index,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
    (∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center time - (family.patch source).center time‖) →
    ‖family.canonicalExteriorAffineCoordinate index (angular time) frequency time (curve time) -
      standardCircleBanach‖ ≤ radius →
    ContinuousAt (diskNormalizedInteractionCurve frequency (fun current =>
      family.canonicalExteriorAffineCoordinate index (angular current) frequency current (curve current))) time := by
  obtain ⟨affineRadius, affinePositive, affines⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_physical_geometric_continuity
  obtain ⟨observableRadius, observablePositive, observables⟩ :=
    diskNormalizedInteractionCurve_exists_uniform_continuity
  refine ⟨min affineRadius observableRadius, lt_min affinePositive observablePositive, ?_⟩
  intro count family index angular curve frequency time distance angularSmall angularContinuous curveContinuous
    angularReal nonzero positive small inside centerGaps correctedSmall
  have correctedContinuous := affines family index (angularSmall.trans_le (min_le_left _ _))
    angularContinuous curveContinuous angularReal nonzero positive small inside centerGaps
  have actual := observables (curve := fun current => family.canonicalExteriorAffineCoordinate index
    (angular current) frequency current (curve current)) (time := time) (frequency := frequency)
    (correctedSmall.trans (min_le_right _ _)) correctedContinuous
  exact actual


end EulerNonuniqueness.Paper.FiniteMovingPatchFamily

