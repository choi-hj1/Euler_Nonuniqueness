import EulerNonuniqueness.Section3.CanonicalInteractionNamedValue

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space
  canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero canonicalForcingNeg canonicalForcingSub

open EulerNonuniqueness.Section6

theorem canonicalNormalizedInteractionCoordinate_exists_uniform_raw_geometric_continuity :
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
    ContinuousAt (fun current => family.canonicalNormalizedInteractionCoordinate index (angular current)
      frequency current (curve current)) time := by
  obtain ⟨radius, positiveRadius, continuous⟩ :=
    canonicalNormalizedInteractionCoordinate_exists_uniform_geometric_continuity
  refine ⟨radius, positiveRadius, ?_⟩
  intro count family index angular curve frequency time distance angularSmall angularContinuous curveContinuous
    angularReal nonzero positive small inside centerGaps correctedSmall
  have actual := continuous family index angularSmall angularContinuous curveContinuous angularReal nonzero
    positive small inside centerGaps correctedSmall
  exact actual.congr (Filter.Eventually.of_forall (fun current =>
    (family.canonicalNormalizedInteractionCoordinate_eq_named_value index angular curve frequency current).symm))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily

