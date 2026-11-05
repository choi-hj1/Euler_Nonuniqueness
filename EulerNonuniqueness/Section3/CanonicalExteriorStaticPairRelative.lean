import EulerNonuniqueness.Section3.CanonicalExteriorStaticResidualIdentity
import EulerNonuniqueness.Section3.ExteriorCoefficientUniformWeights

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  powerFirstJetOperatorGroup exteriorPowerSeriesOperatorSpace gaugeOperatorUniformSecondGroup

open EulerNonuniqueness.Section6

theorem canonicalExteriorStaticCoefficient_summable_weight96 {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance : ℝ)
    (positive : 0 < distance) (small : 192 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖) :
    Summable (fun degree => (96 : ℝ) ^ (degree + 1) *
      ‖family.canonicalExteriorStaticCoefficient index time degree‖) := by
  have integrable := family.subfamilyVorticity_integrable (Finset.univ.erase index) time
  have supportGap := family.subfamily_support_separated (Finset.univ.erase index)
    ((family.patch index).center time) time distance separated
  have coefficientIdentity (degree : ℕ) : family.canonicalExteriorStaticCoefficient index time degree =
      exteriorVorticityCoefficient (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) (family.patch index).radius degree :=
    family.exteriorTaylorCoefficient_eq_vorticityCoefficient (Finset.univ.erase index)
      (family.patch index).center (family.patch index).radius time degree positive separated
  simp_rw [coefficientIdentity]
  exact summable_exteriorVorticityCoefficient_weight integrable _ (family.patch index).radius_positive.le
    positive (by norm_num) supportGap ((div_lt_one positive).mpr (by linarith [(family.patch index).radius_positive]))

theorem canonicalExteriorStaticPhaseResidual_exists_pair_relative_ball :
    ∃ radius > 0, ∃ constant ≥ 0,
      ∀ {firstCount finalCount : ℕ} (firstFamily : FiniteMovingPatchFamily firstCount)
        (finalFamily : FiniteMovingPatchFamily finalCount) (firstIndex : Fin firstCount) (finalIndex : Fin finalCount),
      ∀ firstAngular finalAngular : PeriodicC1HolderHalf,
      ∀ (firstSmall : ‖firstAngular‖ < 1 / 2) (finalSmall : ‖finalAngular‖ < 1 / 2),
      firstAngular ∈ contourContinuousVectorSubmodule → finalAngular ∈ contourContinuousVectorSubmodule →
      (∀ label, star (firstAngular.val.1 label) = firstAngular.val.1 label) →
      (∀ label, star (finalAngular.val.1 label) = finalAngular.val.1 label) →
      ‖diskRelabelCurve firstAngular 1 - standardCircleBanach‖ < min (1 / 3) (min 1 (2 / (3 * Real.pi))) →
      ‖diskRelabelCurve finalAngular 1 - standardCircleBanach‖ < min (1 / 3) (min 1 (2 / (3 * Real.pi))) →
      ∀ firstIncrement finalIncrement : PeriodicC1HolderHalf,
      firstIncrement ∈ contourContinuousVectorSubmodule → finalIncrement ∈ contourContinuousVectorSubmodule →
      contourCentroidFunctional (diskRelabelCurve firstAngular 1 + firstIncrement) =
        contourCentroidFunctional (diskRelabelCurve firstAngular 1) →
      contourCentroidFunctional (diskRelabelCurve finalAngular 1 + finalIncrement) =
        contourCentroidFunctional (diskRelabelCurve finalAngular 1) →
      ∀ {frequency time firstDistance finalDistance : ℝ}, frequency ≠ 0 →
      ∀ (firstPositive : 0 < firstDistance) (finalPositive : 0 < finalDistance)
        (firstSeparated : ∀ source ∈ Finset.univ.erase firstIndex, ∀ position ∈ (firstFamily.patch source).domain time,
          firstDistance ≤ ‖(firstFamily.patch firstIndex).center time - position‖)
        (finalSeparated : ∀ source ∈ Finset.univ.erase finalIndex, ∀ position ∈ (finalFamily.patch source).domain time,
          finalDistance ≤ ‖(finalFamily.patch finalIndex).center time - position‖),
      ∀ (firstScale : 192 * (firstFamily.patch firstIndex).radius ≤ firstDistance)
        (finalScale : 192 * (finalFamily.patch finalIndex).radius ≤ finalDistance),
      let firstBase := diskRelabelCurve firstAngular 1
      let finalBase := diskRelabelCurve finalAngular 1
      let firstData := firstBase + firstIncrement
      let finalData := finalBase + finalIncrement
      let firstShift := firstData - firstFamily.canonicalExteriorAffineCoordinate firstIndex firstAngular frequency time firstData
      let finalShift := finalData - finalFamily.canonicalExteriorAffineCoordinate finalIndex finalAngular frequency time finalData
      ‖firstBase - standardCircleBanach‖ + (‖firstIncrement‖ + ‖finalIncrement‖) + (‖firstShift‖ + ‖finalShift‖) ≤ radius →
      ‖finalBase - standardCircleBanach‖ + (‖firstIncrement‖ + ‖finalIncrement‖) + (‖firstShift‖ + ‖finalShift‖) ≤ radius →
      ‖firstFamily.canonicalExteriorStaticPhaseResidual firstIndex firstAngular frequency time firstDistance firstPositive
          (by linarith [firstScale, (firstFamily.patch firstIndex).radius_positive]) firstSeparated firstData -
        finalFamily.canonicalExteriorStaticPhaseResidual finalIndex finalAngular frequency time finalDistance finalPositive
          (by linarith [finalScale, (finalFamily.patch finalIndex).radius_positive]) finalSeparated finalData‖ ≤
      constant * canonicalExteriorStaticRelativeBudget frequency
        (firstFamily.canonicalExteriorStaticCoefficient firstIndex time)
        (finalFamily.canonicalExteriorStaticCoefficient finalIndex time)
        firstBase finalBase firstIncrement finalIncrement firstShift finalShift
        (firstFamily.relabeledExteriorHigherForcingPrimitive firstIndex firstAngular frequency time)
        (finalFamily.relabeledExteriorHigherForcingPrimitive finalIndex finalAngular frequency time)
        (firstFamily.exteriorStrainModulatedCoefficient firstIndex frequency time)
        (finalFamily.exteriorStrainModulatedCoefficient finalIndex frequency time) := by
  obtain ⟨assemblyRadius, assemblyPositive, constant, nonnegative, assembly⟩ :=
    canonicalExteriorStaticResidual_exists_relative_ball
  refine ⟨min assemblyRadius (1 / 12), lt_min assemblyPositive (by norm_num), constant, nonnegative, ?_⟩
  intro firstCount finalCount firstFamily finalFamily firstIndex finalIndex firstAngular finalAngular
    firstSmall finalSmall firstAngularMember finalAngularMember firstReal finalReal firstNearby finalNearby
    firstIncrement finalIncrement firstMember finalMember firstCentered finalCentered frequency time
    firstDistance finalDistance nonzero firstPositive finalPositive firstSeparated finalSeparated
    firstScale finalScale firstBase finalBase firstData finalData firstShift finalShift firstInside finalInside
  have firstSummable := firstFamily.canonicalExteriorStaticCoefficient_summable_weight96 firstIndex time firstDistance
    firstPositive firstScale firstSeparated
  have finalSummable := finalFamily.canonicalExteriorStaticCoefficient_summable_weight96 finalIndex time finalDistance
    finalPositive finalScale finalSeparated
  have firstTwentyFour := summable_exteriorCoefficientWeight_mono
    (firstFamily.canonicalExteriorStaticCoefficient firstIndex time)
    (by norm_num : (0 : ℝ) ≤ 24) (by norm_num : (24 : ℝ) ≤ 96) firstSummable
  have finalTwentyFour := summable_exteriorCoefficientWeight_mono
    (finalFamily.canonicalExteriorStaticCoefficient finalIndex time)
    (by norm_num : (0 : ℝ) ≤ 24) (by norm_num : (24 : ℝ) ≤ 96) finalSummable
  have firstDataNearby : ‖firstBase - standardCircleBanach + firstIncrement‖ < 1 / 3 := by
    have bound := (norm_add_le (firstBase - standardCircleBanach) firstIncrement).trans
      (by linarith [firstInside.trans (min_le_right _ _), norm_nonneg finalIncrement,
        norm_nonneg firstShift, norm_nonneg finalShift] :
      ‖firstBase - standardCircleBanach‖ + ‖firstIncrement‖ ≤ 1 / 12)
    linarith
  have finalDataNearby : ‖finalBase - standardCircleBanach + finalIncrement‖ < 1 / 3 := by
    have bound := (norm_add_le (finalBase - standardCircleBanach) finalIncrement).trans
      (by linarith [finalInside.trans (min_le_right _ _), norm_nonneg firstIncrement,
        norm_nonneg firstShift, norm_nonneg finalShift] :
      ‖finalBase - standardCircleBanach‖ + ‖finalIncrement‖ ≤ 1 / 12)
    linarith
  have firstIdentity := firstFamily.canonicalExteriorStaticPhaseResidual_eq_staticResidual firstIndex firstAngular
    firstSmall firstReal firstNearby nonzero firstPositive
    (by linarith [(firstFamily.patch firstIndex).radius_positive]) firstSeparated firstIncrement firstDataNearby
    ((div_lt_one firstPositive).mpr (by linarith [(firstFamily.patch firstIndex).radius_positive])) firstTwentyFour
  have finalIdentity := finalFamily.canonicalExteriorStaticPhaseResidual_eq_staticResidual finalIndex finalAngular
    finalSmall finalReal finalNearby nonzero finalPositive
    (by linarith [(finalFamily.patch finalIndex).radius_positive]) finalSeparated finalIncrement finalDataNearby
    ((div_lt_one finalPositive).mpr (by linarith [(finalFamily.patch finalIndex).radius_positive])) finalTwentyFour
  have firstBaseIdentity := fixedRelabelEquivalence_circle firstAngular firstSmall firstReal
  have finalBaseIdentity := fixedRelabelEquivalence_circle finalAngular finalSmall finalReal
  have actual := assembly firstAngular finalAngular firstSmall finalSmall firstAngularMember finalAngularMember
    (by simpa only [firstBaseIdentity] using firstNearby) (by simpa only [finalBaseIdentity] using finalNearby)
    firstIncrement finalIncrement firstShift finalShift
    (firstFamily.relabeledExteriorHigherForcingPrimitive firstIndex firstAngular frequency time)
    (finalFamily.relabeledExteriorHigherForcingPrimitive finalIndex finalAngular frequency time)
    firstMember finalMember (by simpa only [firstBaseIdentity] using firstInside.trans (min_le_left _ _))
    (by simpa only [finalBaseIdentity] using finalInside.trans (min_le_left _ _))
    (by simpa only [firstBaseIdentity] using firstCentered) (by simpa only [finalBaseIdentity] using finalCentered)
    (Circle.exp (frequency * time / 2)) frequency
    (firstFamily.canonicalExteriorStaticCoefficient firstIndex time)
    (finalFamily.canonicalExteriorStaticCoefficient finalIndex time) firstSummable finalSummable
    (firstFamily.exteriorStrainModulatedCoefficient firstIndex frequency time)
    (finalFamily.exteriorStrainModulatedCoefficient finalIndex frequency time)
  rw [firstBaseIdentity, finalBaseIdentity] at actual
  rw [firstIdentity, finalIdentity]
  with_reducible_and_instances
    exact actual

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
