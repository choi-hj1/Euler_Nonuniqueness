import EulerNonuniqueness.Section3.CanonicalExteriorAffineShift
import EulerNonuniqueness.Section3.DiskNormalizedProjectionDifference
import EulerNonuniqueness.Section3.DiskNormalizedSpectralEvolution
import EulerNonuniqueness.Section3.DiskPhysicalSpectralRelabelDefect

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance prefixRecoveryCanonicalC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorAffineCoordinate_exists_uniform_prefix_recovery :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular data : PeriodicC1HolderHalf),
    angular = diskNeutralCLM (diskPhysicalSpectralCoordinate data) → ‖angular‖ ≤ radius →
    (∀ label, star (angular.val.1 label) = angular.val.1 label) →
    ∀ {frequency time distance weight control : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
    4 * (family.patch index).radius ≤ distance →
    (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖) →
    (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time)
      ((family.patch index).center time) position) ≤ weight →
    ‖data - standardCircleBanach‖ < radius →
    ‖diskRelabelCurve angular 1 - standardCircleBanach‖ + ‖data - diskRelabelCurve angular 1‖ ≤ radius →
    weight / |frequency| ≤ radius → contourAreaFunctional data = Real.pi →
    contourCentroidFunctional data = 0 →
    ‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate data)‖ ≤ control →
    weight / |frequency| ≤ control → control ≤ 1 →
    ‖data - diskRelabelCurve angular 1‖ ≤ constant * control ∧
    ‖diskPhysicalTransverseProjection (diskNormalizedSpectralCoordinate
      (family.canonicalExteriorAffineCoordinate index angular frequency time data))‖ ≤ constant * control := by
  obtain ⟨defectRadius, defectPositive, defectConstant, defectOne, defects⟩ :=
    diskPhysicalSpectralCoordinate_exists_uniform_relabel_defect
  obtain ⟨projectionRadius, projectionPositive, projectionConstant, projectionOne, projections⟩ :=
    diskNormalizedSpectralCoordinate_exists_uniform_projection_difference
  obtain ⟨shiftRadius, shiftPositive, shifts⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_shift_admissibility projectionRadius projectionPositive
  obtain ⟨nearRadius, nearPositive, nearConstant, nearOne, nears⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_near_identity_bound
  let radius := min defectRadius (min shiftRadius nearRadius)
  let constant := defectConstant + 1 + projectionConstant * nearConstant * (1 + defectConstant)
  have constantOne : 1 ≤ constant := by
    have productNonnegative : 0 ≤ projectionConstant * nearConstant * (1 + defectConstant) := by positivity
    dsimp only [constant]
    linarith
  have defectLe : radius ≤ defectRadius := min_le_left _ _
  have shiftLe : radius ≤ shiftRadius := (min_le_right _ _).trans (min_le_left _ _)
  have nearLe : radius ≤ nearRadius := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_⟩
  intro count family index angular data angularIdentity angularSmall realValues frequency time distance weight control
    nonzero positive weightNonnegative small separated weightBound dataSmall shapeSmall frequencySmall area centered
    transverseBound epsilonBound controlOne
  have defect := defects data (dataSmall.trans_le defectLe) area
  rw [← angularIdentity] at defect
  have shiftAt := shifts family index angular (data - diskRelabelCurve angular 1)
    (angularSmall.trans shiftLe) realValues nonzero positive weightNonnegative small separated weightBound
    (shapeSmall.trans shiftLe) (frequencySmall.trans shiftLe)
  have nearAt := nears family index angular (angularSmall.trans nearLe) realValues nonzero positive
    weightNonnegative small separated weightBound data
  generalize affineEq : family.canonicalExteriorAffineCoordinate index angular frequency time = affine at shiftAt nearAt ⊢
  generalize baseEq : diskRelabelCurve angular 1 = base at shiftAt nearAt defect ⊢
  simp only [add_sub_cancel] at shiftAt
  have projectionAt := projections data (affine data) shiftAt area centered
  rw [norm_sub_rev] at nearAt
  generalize originalEq : diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate data) = original
    at defect projectionAt transverseBound
  generalize correctedEq : diskPhysicalTransverseProjection
    (diskPhysicalSpectralCoordinate (contourAreaCentroidNormalization (affine data))) = corrected at projectionAt ⊢
  have controlNonnegative : 0 ≤ control := (norm_nonneg original).trans transverseBound
  have relativeBound := defect.trans (mul_le_mul_of_nonneg_left transverseBound (by linarith : 0 ≤ defectConstant))
  have relativeCoarse : ‖data - base‖ ≤ defectConstant :=
    relativeBound.trans (by nlinarith)
  have shiftBound : ‖data - affine data‖ ≤ nearConstant * control * (1 + defectConstant) := by
    apply nearAt.trans
    have first := mul_le_mul_of_nonneg_right epsilonBound (by linarith : 0 ≤ nearConstant)
    have scaled := mul_le_mul_of_nonneg_right
      (by simpa only [mul_comm] using first) (by positivity : 0 ≤ 1 + ‖data - base‖)
    exact scaled.trans (mul_le_mul_of_nonneg_left (by linarith : 1 + ‖data - base‖ ≤ 1 + defectConstant)
      (by positivity : 0 ≤ nearConstant * control))
  have correctedBound : ‖corrected‖ ≤ control + projectionConstant * (nearConstant * control * (1 + defectConstant)) := by
    have triangle : ‖corrected‖ ≤ ‖corrected - original‖ + ‖original‖ := by
      simpa only [sub_add_cancel] using norm_add_le (corrected - original) original
    have difference := projectionAt.trans
      (mul_le_mul_of_nonneg_left shiftBound (by linarith : 0 ≤ projectionConstant))
    exact triangle.trans (by linarith)
  constructor
  · apply relativeBound.trans
    have extra : 0 ≤ (1 + projectionConstant * nearConstant * (1 + defectConstant)) * control := by positivity
    dsimp only [constant]
    nlinarith
  · rw [diskNormalizedSpectralCoordinate, correctedEq]
    apply correctedBound.trans
    have extra := mul_nonneg (by linarith : 0 ≤ defectConstant) controlNonnegative
    dsimp only [constant]
    nlinarith

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
