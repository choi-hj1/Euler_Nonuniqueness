import EulerNonuniqueness.Section3.CanonicalInteractionInitialBound
import EulerNonuniqueness.Section3.DiskNormalizedTransverseRecovery
import EulerNonuniqueness.Section3.DiskPhysicalScaledGroupRecovery

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance canonicalInteractionRecoveryC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

open EulerNonuniqueness.Section6

theorem canonicalNormalizedInteractionCoordinate_exists_uniform_transverse_recovery :
    ∃ radius > 0, ∃ recovery ≥ 0, ∃ loss ≥ 0,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular data : PeriodicC1HolderHalf), ‖angular‖ ≤ radius →
      (∀ label, star (angular.val.1 label) = angular.val.1 label) →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      4 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight →
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ + ‖data - diskRelabelCurve angular 1‖ ≤ radius →
      weight / |frequency| ≤ radius → contourAreaFunctional data = Real.pi → contourCentroidFunctional data = 0 →
      ‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate data)‖ ≤
        recovery * ‖family.canonicalNormalizedInteractionCoordinate index angular frequency time data‖ +
          loss * (weight / |frequency|) := by
  obtain ⟨recoveryRadius, recoveryPositive, recoveryConstant, recoveryOne, recoveries⟩ :=
    diskNormalizedQuadraticObservable_exists_uniform_transverse_recovery
  obtain ⟨shiftRadius, shiftPositive, shifts⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_shift_admissibility recoveryRadius recoveryPositive
  obtain ⟨affineRadius, affinePositive, affineConstant, affineOne, affines⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_near_identity_bound
  let radius := min shiftRadius (min affineRadius 1)
  refine ⟨radius, by dsimp [radius]; positivity,
    recoveryConstant * diskPhysicalGroupBound,
      mul_nonneg (by linarith) diskPhysicalGroupBound_nonnegative,
    2 * recoveryConstant * affineConstant, by positivity, ?_⟩
  intro count family index angular data angularSmall realValues frequency time distance weight nonzero positive
    weightNonnegative small separated weightBound shapeSmall frequencySmall area centered
  have shifted := shifts family index angular (data - diskRelabelCurve angular 1)
    (angularSmall.trans (min_le_left _ _)) realValues nonzero positive weightNonnegative small separated weightBound
    (shapeSmall.trans (min_le_left _ _)) (frequencySmall.trans (min_le_left _ _))
  have sumIdentity : diskRelabelCurve angular 1 + (data - diskRelabelCurve angular 1) = data := by abel
  rw [sumIdentity] at shifted
  have shiftBound := affines family index angular
    (angularSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) realValues nonzero positive
    weightNonnegative small separated weightBound data
  have relativeOne : ‖data - diskRelabelCurve angular 1‖ ≤ 1 := by
    have total := shapeSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith [norm_nonneg (diskRelabelCurve angular 1 - standardCircleBanach)]
  have recovered := recoveries data
    (family.canonicalExteriorAffineCoordinate index angular frequency time data) shifted area centered
  unfold canonicalNormalizedInteractionCoordinate canonicalNormalizedQuadraticObservable
  generalize coordinateEq : family.canonicalExteriorAffineCoordinate index angular frequency time = coordinate
    at shiftBound shifted recovered ⊢
  generalize correctedEq : coordinate data = corrected at shiftBound shifted recovered ⊢
  change ‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate data)‖ ≤
    recoveryConstant * (‖diskNormalizedQuadraticObservable corrected‖ + ‖data - corrected‖) at recovered
  have groupBound := diskPhysicalScaledGroup_norm_recovery frequency time (diskNormalizedQuadraticObservable corrected)
  generalize projectedEq : diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate data) = projected
    at recovered ⊢
  generalize observableEq : diskNormalizedQuadraticObservable corrected = observable at recovered groupBound ⊢
  generalize groupEq : diskPhysicalScaledGroup frequency (-time) observable = groupValue at groupBound ⊢
  have actualShift : ‖data - corrected‖ ≤ 2 * affineConstant * (weight / |frequency|) := by
    rw [norm_sub_rev]
    have affineNonnegative : 0 ≤ affineConstant := by linarith
    have coefficientNonnegative := mul_nonneg affineNonnegative
      (div_nonneg weightNonnegative (abs_nonneg frequency))
    calc
      _ ≤ affineConstant * (weight / |frequency|) * 2 := shiftBound.trans
        (mul_le_mul_of_nonneg_left (by linarith : 1 + ‖data - diskRelabelCurve angular 1‖ ≤ 2)
          coefficientNonnegative)
      _ = _ := by ring
  have enlarged := recovered.trans (mul_le_mul_of_nonneg_left
    (add_le_add groupBound actualShift) (show 0 ≤ recoveryConstant by linarith))
  exact enlarged.trans_eq (by ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
