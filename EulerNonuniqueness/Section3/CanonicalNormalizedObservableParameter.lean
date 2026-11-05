import EulerNonuniqueness.Section3.DiskQuadraticObservableRecovery
import EulerNonuniqueness.Section3.CanonicalExteriorAffineParameter
import EulerNonuniqueness.Section3.CanonicalExteriorAffineShift

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

def canonicalNormalizedQuadraticObservable {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (angular : PeriodicC1HolderHalf) (frequency time : ℝ)
    (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskNormalizedQuadraticObservable (family.canonicalExteriorAffineCoordinate index angular frequency time data)

theorem canonicalNormalizedQuadraticObservable_exists_uniform_parameter_lipschitz :
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
      ∀ data : PeriodicC1HolderHalf,
      ‖diskRelabelCurve first 1 - standardCircleBanach‖ + ‖data - diskRelabelCurve first 1‖ ≤ radius →
      ‖diskRelabelCurve second 1 - standardCircleBanach‖ + ‖data - diskRelabelCurve second 1‖ ≤ radius →
      ‖family.canonicalNormalizedQuadraticObservable index first frequency time data -
        family.canonicalNormalizedQuadraticObservable index second frequency time data‖ ≤
        constant * (weight / |frequency|) * (1 + ‖data - diskRelabelCurve second 1‖) * ‖first - second‖ := by
  obtain ⟨observableRadius, observablePositive, observableConstant, observableOne, observableBounds⟩ :=
    diskNormalizedQuadraticObservable_exists_uniform_difference_bound
  obtain ⟨shiftRadius, shiftPositive, shiftBounds⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_shift_admissibility observableRadius observablePositive
  obtain ⟨parameterRadius, parameterPositive, parameterConstant, parameterOne, parameterBounds⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_parameter_lipschitz
  let radius := min shiftRadius parameterRadius
  let constant := observableConstant * parameterConstant
  have constantOne : 1 ≤ constant := by dsimp [constant]; nlinarith
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_⟩
  intro count family index first second firstSmall secondSmall firstReal secondReal frequency time distance weight
    nonzero positive weightNonnegative small separated weightBound frequencySmall data firstNear secondNear
  have smallFour : 4 * (family.patch index).radius ≤ distance := by
    linarith [(family.patch index).radius_positive]
  have shifted (angular : PeriodicC1HolderHalf) (angularSmall : ‖angular‖ ≤ shiftRadius)
      (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
      (shapeSmall : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ + ‖data - diskRelabelCurve angular 1‖ ≤ shiftRadius) :
      ‖family.canonicalExteriorAffineCoordinate index angular frequency time data - standardCircleBanach‖ ≤ observableRadius := by
    have actual := shiftBounds family index angular (data - diskRelabelCurve angular 1) angularSmall realValues
      nonzero positive weightNonnegative smallFour separated weightBound shapeSmall
      (frequencySmall.trans (min_le_left _ _))
    have reconstruct : diskRelabelCurve angular 1 + (data - diskRelabelCurve angular 1) = data := by abel
    rw [reconstruct] at actual
    have triangle := norm_add_le
      (data - standardCircleBanach) (family.canonicalExteriorAffineCoordinate index angular frequency time data - data)
    have identity : data - standardCircleBanach +
        (family.canonicalExteriorAffineCoordinate index angular frequency time data - data) =
        family.canonicalExteriorAffineCoordinate index angular frequency time data - standardCircleBanach := by abel
    rw [identity, norm_sub_rev (family.canonicalExteriorAffineCoordinate index angular frequency time data) data] at triangle
    exact triangle.trans actual
  have firstShift := shifted first (firstSmall.trans (min_le_left _ _)) firstReal (firstNear.trans (min_le_left _ _))
  have secondShift := shifted second (secondSmall.trans (min_le_left _ _)) secondReal (secondNear.trans (min_le_left _ _))
  have actual := observableBounds
    (family.canonicalExteriorAffineCoordinate index first frequency time data)
    (family.canonicalExteriorAffineCoordinate index second frequency time data) firstShift secondShift
  have parameter := parameterBounds family index first second
    (firstSmall.trans (min_le_right _ _)) (secondSmall.trans (min_le_right _ _)) firstReal secondReal
    nonzero positive weightNonnegative small separated weightBound data
  unfold canonicalNormalizedQuadraticObservable
  exact actual.trans ((mul_le_mul_of_nonneg_left parameter (by linarith)).trans_eq (by dsimp only [constant]; ring))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
