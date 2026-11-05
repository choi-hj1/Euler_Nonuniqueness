import EulerNonuniqueness.Section3.CanonicalExteriorAffinePhaseBound
import EulerNonuniqueness.Section3.CanonicalPhysicalAmplitudeErrorBound
import EulerNonuniqueness.General.PhaseAmplitudeErrorBudget

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorAffineMaterialError_exists_uniform_bound :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular direction : PeriodicC1HolderHalf) (angularSmall : ‖angular‖ < 1 / 2), ‖angular‖ ≤ radius →
      angular ∈ contourContinuousVectorSubmodule → direction ∈ contourContinuousVectorSubmodule →
      (∀ label, star (angular.val.1 label) = angular.val.1 label) →
      ∀ {frequency time distance weight mass : ℝ}, frequency ≠ 0 →
      time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime →
      (∀ label, (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label)) →
      (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid →
      ∀ (positive : 0 < distance), 0 ≤ weight → 0 ≤ mass →
      ∀ (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖),
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight →
      (∫ position, |family.patchVorticity time index position|) ≤ mass →
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ + ‖direction‖ ≤ radius →
      weight / |frequency| ≤ radius →
      contourCentroidFunctional (diskRelabelCurve angular 1 + direction) =
        contourCentroidFunctional (diskRelabelCurve angular 1) →
      ‖family.canonicalExteriorAffinePhaseField index angular frequency time distance positive
          (by linarith [(family.patch index).radius_positive]) separated (diskRelabelCurve angular 1 + direction) -
        fixedRelabelEquivalence angular angularSmall
          (family.exteriorAmplitudeDerivativePrimitive index frequency time) -
        family.exteriorStrainAmplitudeCorrection index angular frequency time direction -
        frequency • diskEulerRotatingField
          (family.canonicalExteriorAffineCoordinate index angular frequency time (diskRelabelCurve angular 1 + direction))‖ ≤
        constant * (weight * ‖direction‖ ^ 2 + weight * ((family.patch index).radius / distance) * ‖direction‖ +
          (weight ^ 2 + mass * weight / distance ^ 2) / |frequency|) := by
  obtain ⟨phaseRadius, phasePositive, phaseConstant, phaseOne, phaseBounds⟩ :=
    canonicalExteriorAffinePhaseField_exists_uniform_error_bound
  obtain ⟨amplitudeRadius, amplitudePositive, amplitudeConstant, amplitudeOne, amplitudeBounds⟩ :=
    exteriorAffineAmplitudeError_exists_uniform_value_bound
  let radius := min phaseRadius (min amplitudeRadius (1 / 4))
  let constant := phaseConstant + 2 * amplitudeConstant + 1
  have phaseLe : radius ≤ phaseRadius := min_le_left _ _
  have amplitudeLe : radius ≤ amplitudeRadius := (min_le_right _ _).trans (min_le_left _ _)
  have quarterLe : radius ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨radius, by dsimp [radius]; positivity, constant, by dsimp [constant]; linarith, ?_⟩
  intro count family index angular direction angularSmall angularNear angularMember directionMember realValues frequency time distance weight mass
    nonzero inside material centered positive weightNonnegative massNonnegative small separated weightBound massBound
    shapeSmall frequencySmall centroidEqual
  have phaseActual := phaseBounds family index angular direction (angularNear.trans phaseLe) angularMember directionMember
    realValues nonzero positive weightNonnegative small separated weightBound (shapeSmall.trans phaseLe)
    (frequencySmall.trans phaseLe) centroidEqual
  have smallEight : 8 * (family.patch index).radius ≤ distance := by linarith [(family.patch index).radius_positive]
  have amplitudeActual := amplitudeBounds family index angular angularSmall (angularNear.trans amplitudeLe)
    nonzero inside material centered positive weightNonnegative massNonnegative smallEight separated weightBound massBound direction
  have directionOne : ‖direction‖ ≤ 1 := by
    linarith [norm_nonneg (diskRelabelCurve angular 1 - standardCircleBanach), shapeSmall.trans quarterLe]
  have patchRadiusNonnegative : 0 ≤ (family.patch index).radius := (family.patch index).radius_positive.le
  have thirdNonnegative : 0 ≤ (weight ^ 2 + mass * weight / distance ^ 2) / |frequency| := by positivity
  have selfLe : weight ^ 2 / |frequency| ≤ (weight ^ 2 + mass * weight / distance ^ 2) / |frequency| :=
    div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (abs_nonneg frequency)
  have phaseEstimate := phaseActual.trans (mul_le_mul_of_nonneg_left (add_le_add_left selfLe _) (by linarith : 0 ≤ phaseConstant))
  have amplitudeEstimate := amplitudeActual.trans (mul_le_mul_of_nonneg_left (by linarith : 1 + ‖direction‖ ≤ 2)
    (show 0 ≤ amplitudeConstant * (weight ^ 2 + mass * weight / distance ^ 2) / |frequency| by positivity))
  dsimp only
  generalize baseEq : diskRelabelCurve angular 1 = base at phaseEstimate amplitudeEstimate ⊢
  generalize phaseEq : family.canonicalExteriorAffinePhaseField index angular frequency time distance positive smallEight separated
    (base + direction) = phaseValue at phaseEstimate ⊢
  generalize selfEq : frequency • diskEulerRotatingField
    (family.canonicalExteriorAffineCoordinate index angular frequency time (base + direction)) = selfValue at phaseEstimate ⊢
  generalize amplitudeEq : fixedRelabelEquivalence angular angularSmall
    (family.exteriorAmplitudeDerivativePrimitive index frequency time) +
    family.exteriorStrainAmplitudeCorrection index angular frequency time direction = amplitudeValue at amplitudeEstimate
  have total := add_le_add phaseEstimate amplitudeEstimate
  have firstNonnegative : 0 ≤ weight * ‖direction‖ ^ 2 := by positivity
  have secondNonnegative : 0 ≤ weight * ((family.patch index).radius / distance) * ‖direction‖ := by positivity
  have scalar : phaseConstant * (weight * ‖direction‖ ^ 2 + weight * ((family.patch index).radius / distance) * ‖direction‖ +
      (weight ^ 2 + mass * weight / distance ^ 2) / |frequency|) +
      amplitudeConstant * (weight ^ 2 + mass * weight / distance ^ 2) / |frequency| * 2 ≤
      constant * (weight * ‖direction‖ ^ 2 + weight * ((family.patch index).radius / distance) * ‖direction‖ +
        (weight ^ 2 + mass * weight / distance ^ 2) / |frequency|) := by
    have numerical := EulerNonuniqueness.General.phase_amplitude_error_budget phaseConstant amplitudeConstant
      (weight * ‖direction‖ ^ 2) (weight * ((family.patch index).radius / distance) * ‖direction‖)
      ((weight ^ 2 + mass * weight / distance ^ 2) / |frequency|) (by linarith : 0 ≤ amplitudeConstant)
      firstNonnegative secondNonnegative thirdNonnegative
    convert numerical using 1 <;> dsimp [constant] <;> ring
  have algebra : phaseValue -
      fixedRelabelEquivalence angular angularSmall (family.exteriorAmplitudeDerivativePrimitive index frequency time) -
      family.exteriorStrainAmplitudeCorrection index angular frequency time direction - selfValue =
      (phaseValue - selfValue) - amplitudeValue := by rw [← amplitudeEq]; abel
  rw [algebra]
  exact (norm_sub_le _ _).trans (total.trans scalar)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
