import EulerNonuniqueness.Section3.CanonicalExteriorAffineSelfError
import EulerNonuniqueness.Section3.CanonicalExteriorTailSelfError
import EulerNonuniqueness.Section3.CanonicalLeadingModulatedStrainBound
import EulerNonuniqueness.Section3.CanonicalExteriorHigherDifference
import EulerNonuniqueness.Section3.CanonicalPhysicalCorrectionBound
import EulerNonuniqueness.Section3.DiskForcingPhaseRotation
import EulerNonuniqueness.General.ThreeScaleErrorBudget

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

theorem canonicalExteriorAffineError_exists_uniform_norm_budget :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular direction : PeriodicC1HolderHalf), ‖angular‖ ≤ radius →
      angular ∈ contourContinuousVectorSubmodule → direction ∈ contourContinuousVectorSubmodule →
      (∀ label, star (angular.val.1 label) = angular.val.1 label) →
      ∀ {frequency time distance weight : ℝ} (nonzero : frequency ≠ 0) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
        (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖)
        (weightBound : (∫ position, inverseSquareVorticityWeight
          (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight),
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ + ‖direction‖ ≤ radius → weight / |frequency| ≤ radius →
      contourCentroidFunctional (diskRelabelCurve angular 1 + direction) = contourCentroidFunctional (diskRelabelCurve angular 1) →
      let base := diskRelabelCurve angular 1
      let data := base + direction
      let shifted := family.canonicalExteriorAffineCoordinate index angular frequency time data
      let phase := Circle.exp (frequency * time / 2)
      let smaller : 8 * (family.patch index).radius ≤ distance := by linarith [(family.patch index).radius_positive]
      let higher := family.canonicalExteriorHigherContourField index time distance positive smaller separated phase
      ‖frequency • diskEulerRotatingField data - frequency • (fderiv ℝ diskEulerRotatingField data (data - shifted)) -
          frequency • diskEulerRotatingField shifted‖ +
        ‖movingStrainAffineResidual base (family.exteriorStrainModulatedCoefficient index frequency time) data‖ +
        ‖higher data - higher base‖ +
        ‖frequency • ((fderiv ℝ diskEulerRotatingField data - fderiv ℝ diskEulerRotatingField base)
          (family.relabeledExteriorHigherForcingPrimitive index angular frequency time))‖ +
        ‖family.exteriorStrainPhysicalCorrection index angular frequency time
          (family.canonicalProjectedExteriorContourField index time distance positive smaller separated phase data)‖ ≤
        constant * (weight * ‖direction‖ ^ 2 + weight * ((family.patch index).radius / distance) * ‖direction‖ + weight ^ 2 / |frequency|) := by
  obtain ⟨selfRadius, selfPositive, selfConstant, selfOne, selfBounds⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_self_error
  obtain ⟨leadingRadius, leadingPositive, leadingConstant, leadingOne, leadingBounds⟩ :=
    canonicalLeadingModulatedStrainResidual_exists_uniform_bound
  obtain ⟨higherRadius, higherPositive, _, higherConstant, higherOne, higherBounds⟩ :=
    canonicalExteriorHigherContourField_exists_uniform_difference_bound
  obtain ⟨tailRadius, tailPositive, tailConstant, tailOne, tailBounds⟩ :=
    relabeledExteriorHigherForcingPrimitive_exists_uniform_self_difference_bound
  obtain ⟨transportRadius, transportPositive, transportConstant, transportOne, transportBounds⟩ :=
    exteriorStrainPhysicalCorrection_canonicalField_exists_uniform_bound
  let radius := min selfRadius (min leadingRadius (min higherRadius (min tailRadius transportRadius)))
  let constant := selfConstant + leadingConstant + higherConstant + tailConstant + transportConstant + 1
  have selfNonnegative : 0 ≤ selfConstant := by linarith
  have leadingNonnegative : 0 ≤ leadingConstant := by linarith
  have higherNonnegative : 0 ≤ higherConstant := by linarith
  have tailNonnegative : 0 ≤ tailConstant := by linarith
  have transportNonnegative : 0 ≤ transportConstant := by linarith
  have selfLe : radius ≤ selfRadius := min_le_left _ _
  have leadingLe : radius ≤ leadingRadius := (min_le_right _ _).trans (min_le_left _ _)
  have higherLe : radius ≤ higherRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have tailLe : radius ≤ tailRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have transportLe : radius ≤ transportRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨radius, by dsimp [radius]; positivity, constant, by dsimp [constant]; linarith, ?_⟩
  intro count family index angular direction angularSmall angularMember directionMember realValues
    frequency time distance weight nonzero positive weightNonnegative small separated weightBound inside frequencySmall centered
  let base := diskRelabelCurve angular 1
  let data := base + direction
  let phase := Circle.exp (frequency * time / 2)
  have small4 : 4 * (family.patch index).radius ≤ distance := by linarith [(family.patch index).radius_positive]
  have small48 : 48 * (family.patch index).radius ≤ distance := by linarith [(family.patch index).radius_positive]
  have selfEstimate := selfBounds family index angular direction (angularSmall.trans selfLe) realValues nonzero positive
    weightNonnegative small4 separated weightBound (inside.trans selfLe) (frequencySmall.trans selfLe)
  have leadingEstimate := leadingBounds family index frequency time distance weight positive weightNonnegative separated weightBound
    angular (angularSmall.trans leadingLe) angularMember realValues direction (inside.trans leadingLe) directionMember centered
  have higherEstimate := higherBounds family index time distance weight positive weightNonnegative small separated weightBound
    phase (base - standardCircleBanach) direction (inside.trans higherLe)
  have baseReconstruct : standardCircleBanach + (base - standardCircleBanach) = base := by abel
  have dataReconstruct : standardCircleBanach + (base - standardCircleBanach + direction) = data := by dsimp [data]; abel
  have tailEstimate := tailBounds family index angular direction (angularSmall.trans tailLe) realValues nonzero positive
    weightNonnegative small4 separated weightBound (inside.trans tailLe)
  have dataSmall : ‖data - standardCircleBanach‖ ≤ radius := by
    have identity : data - standardCircleBanach = (base - standardCircleBanach) + direction := by dsimp [data]; abel
    rw [identity]
    exact (norm_add_le _ _).trans inside
  have transportEstimate := transportBounds family index time distance weight frequency positive weightNonnegative small48 separated
    weightBound phase angular (data - standardCircleBanach) (angularSmall.trans transportLe) (dataSmall.trans transportLe)
  have reconstruct : standardCircleBanach + (data - standardCircleBanach) = data := by abel
  unfold canonicalExteriorHigherContourField at higherEstimate ⊢
  dsimp only [base, data, phase] at selfEstimate leadingEstimate higherEstimate tailEstimate transportEstimate ⊢
  generalize sourceEq : family.canonicalProjectedExteriorContourField index time distance positive
    (by linarith [(family.patch index).radius_positive]) separated (Circle.exp (frequency * time / 2)) = sourceField
    at higherEstimate transportEstimate ⊢
  dsimp only [base, data] at baseReconstruct dataReconstruct reconstruct
  generalize baseEq : diskRelabelCurve angular 1 = shape
    at selfEstimate leadingEstimate higherEstimate tailEstimate transportEstimate baseReconstruct dataReconstruct reconstruct ⊢
  rw [baseReconstruct, dataReconstruct] at higherEstimate
  rw [reconstruct] at transportEstimate
  have summed := add_le_add (add_le_add (add_le_add (add_le_add selfEstimate leadingEstimate) higherEstimate) tailEstimate) transportEstimate
  have numerical := EulerNonuniqueness.General.five_term_three_scale_bound selfConstant leadingConstant higherConstant tailConstant transportConstant
    (weight * ‖direction‖ ^ 2) (weight * ((family.patch index).radius / distance) * ‖direction‖) (weight ^ 2 / |frequency|)
    selfNonnegative leadingNonnegative higherNonnegative tailNonnegative transportNonnegative
    (by positivity)
    (mul_nonneg (mul_nonneg weightNonnegative
      (div_nonneg (family.patch index).radius_positive.le positive.le)) (norm_nonneg direction))
    (by positivity)
  exact summed.trans (by convert numerical using 1 <;> dsimp [constant] <;> ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
