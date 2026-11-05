import EulerNonuniqueness.Section3.CanonicalExteriorFirstAmplitudeRelative

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorFirstAmplitudeError_exists_material_relative_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (firstAngular finalAngular : PeriodicC1HolderHalf),
      ∀ (firstSmall : ‖firstAngular‖ < 1 / 2) (finalSmall : ‖finalAngular‖ < 1 / 2),
      ‖firstAngular‖ ≤ radius → ‖finalAngular‖ ≤ radius →
      (∀ label, star (firstAngular.val.1 label) = firstAngular.val.1 label) →
      (∀ label, star (finalAngular.val.1 label) = finalAngular.val.1 label) →
      ‖diskRelabelCurve firstAngular 1‖ ≤ 3 → ‖diskRelabelCurve finalAngular 1‖ ≤ 3 →
      ∀ {frequency time distance weight mass : ℝ}, frequency ≠ 0 →
      time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime →
      (∀ label, (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label)) →
      (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid →
      0 < distance → 0 ≤ weight → 0 ≤ mass → 192 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      (∫ position, |family.patchVorticity time index position|) ≤ mass →
      ∀ firstData finalData : PeriodicC1HolderHalf,
      ‖(fixedRelabelEquivalence firstAngular firstSmall
          (family.exteriorAmplitudeDerivativePrimitive index frequency time) +
        family.exteriorStrainAmplitudeCorrection index firstAngular frequency time
          (firstData - diskRelabelCurve firstAngular 1)) -
        (fixedRelabelEquivalence finalAngular finalSmall
          (family.exteriorAmplitudeDerivativePrimitive index frequency time) +
        family.exteriorStrainAmplitudeCorrection index finalAngular frequency time
          (finalData - diskRelabelCurve finalAngular 1))‖ ≤
      constant * ((12 * (46 * weight ^ 2 / Real.pi ^ 2 +
        6 * mass * weight / (Real.pi ^ 2 * distance ^ 2))) / |frequency|) *
        (‖firstData - finalData‖ +
          (1 + ‖finalData - diskRelabelCurve finalAngular 1‖) * ‖firstAngular - finalAngular‖) := by
  obtain ⟨radius, positive, constant, one, relative⟩ := canonicalExteriorFirstAmplitudeError_exists_relative_ball
  refine ⟨radius, positive, constant, one, ?_⟩
  intro count family index firstAngular finalAngular firstSmall finalSmall firstInside finalInside firstReal finalReal
    firstBound finalBound frequency time distance weight mass nonzero inside material centered positiveDistance
    weightNonnegative massNonnegative small separated weightBound massBound firstData finalData
  have weighted := family.exteriorMaterialCoefficientDerivative_stronger_weight_bounds index inside material centered
    positiveDistance weightNonnegative massNonnegative (factor := 12) (by norm_num)
    (by linarith [(family.patch index).radius_positive]) separated weightBound massBound
  norm_num only [show (2 : ℝ) * 12 = 24 by norm_num] at weighted
  have actual := relative family index firstAngular finalAngular firstSmall finalSmall firstInside finalInside
    firstReal finalReal firstBound finalBound nonzero weighted.1 firstData finalData
  have scalar := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right weighted.2 (abs_nonneg frequency))
      (by linarith : 0 ≤ constant))
    (by positivity : 0 ≤ ‖firstData - finalData‖ +
      (1 + ‖finalData - diskRelabelCurve finalAngular 1‖) * ‖firstAngular - finalAngular‖)
  exact actual.trans scalar

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
