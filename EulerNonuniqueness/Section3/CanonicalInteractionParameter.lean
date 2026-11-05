import EulerNonuniqueness.Section3.CanonicalNormalizedObservableSmallParameter
import EulerNonuniqueness.Section3.DiskPhysicalScaledGroup

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

def canonicalNormalizedInteractionCoordinate {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (angular : PeriodicC1HolderHalf) (frequency time : ℝ)
    (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskPhysicalScaledGroup frequency (-time)
    (family.canonicalNormalizedQuadraticObservable index angular frequency time data)

theorem canonicalNormalizedInteractionCoordinate_exists_uniform_parameter_bound :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (first second : PeriodicC1HolderHalf), ‖first‖ ≤ radius → ‖second‖ ≤ radius →
      (∀ label, star (first.val.1 label) = first.val.1 label) →
      (∀ label, star (second.val.1 label) = second.val.1 label) →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      48 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight →
      weight / |frequency| ≤ radius →
      ∀ data : PeriodicC1HolderHalf, ‖data - standardCircleBanach‖ ≤ radius →
      ‖family.canonicalNormalizedInteractionCoordinate index first frequency time data -
        family.canonicalNormalizedInteractionCoordinate index second frequency time data‖ ≤
        constant * (weight / |frequency|) * ‖first - second‖ := by
  obtain ⟨radius, positiveRadius, parameterConstant, parameterOne, parameters⟩ :=
    canonicalNormalizedQuadraticObservable_exists_uniform_small_parameter_bound
  let constant := diskPhysicalGroupBound * parameterConstant + 1
  have constantOne : 1 ≤ constant := by
    have productNonnegative := mul_nonneg diskPhysicalGroupBound_nonnegative (show 0 ≤ parameterConstant by linarith)
    dsimp only [constant]
    linarith
  refine ⟨radius, positiveRadius, constant, constantOne, ?_⟩
  intro count family index first second firstSmall secondSmall firstReal secondReal frequency time distance weight
    nonzero positive weightNonnegative small separated weightBound frequencySmall data dataSmall
  have actual := parameters family index first second firstSmall secondSmall firstReal secondReal nonzero
    positive weightNonnegative small separated weightBound frequencySmall data dataSmall
  unfold canonicalNormalizedInteractionCoordinate
  rw [← map_sub]
  have estimate := (diskPhysicalScaledGroup_norm_bound frequency (-time) _).trans
    (mul_le_mul_of_nonneg_left actual diskPhysicalGroupBound_nonnegative)
  have coefficientLe : diskPhysicalGroupBound * parameterConstant ≤ constant := by dsimp only [constant]; linarith
  have enlarged := mul_le_mul_of_nonneg_right coefficientLe
    (mul_nonneg (div_nonneg weightNonnegative (abs_nonneg frequency)) (norm_nonneg (first - second)))
  exact estimate.trans (by convert enlarged using 1 <;> ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
