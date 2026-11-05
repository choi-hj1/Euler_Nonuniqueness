import EulerNonuniqueness.Section3.CanonicalExteriorCommonWeightedInverse
import EulerNonuniqueness.Section3.DiskSpectralQuadraticWeightedInverse

noncomputable section

open Metric Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6 EulerNonuniqueness.General

theorem canonicalExteriorCommonRawSpectralCoordinate_exists_quadratic_weighted_inverse_ball :
    ∃ radius > 0, ∃ forcingRadius > 0, ∃ mapConstant ≥ 1,
      ∃ quadraticRadius > 0, ∃ quadraticConstant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (first final : PeriodicC1HolderHalf), first ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea first = Real.pi → diskSpectralTubularArea final = Real.pi →
      contourCentroidFunctional (diskPhysicalSpectralChart first) = 0 →
      contourCentroidFunctional (diskPhysicalSpectralChart final) = 0 →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      48 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      weight / |frequency| ≤ forcingRadius →
      ∀ {neutralWeight : ℝ}, 0 ≤ neutralWeight → neutralWeight ≤ 1 →
      (‖diskPhysicalTransverseProjection‖ + ‖diskNeutralCLM‖) *
        (mapConstant * (weight / |frequency|)) ≤ neutralWeight / 2 →
      let firstCorrected := family.canonicalExteriorCommonRawSpectralCoordinate index frequency time first
      let finalCorrected := family.canonicalExteriorCommonRawSpectralCoordinate index frequency time final
      ‖diskRelabelNeutralCLM firstCorrected‖ ≤ quadraticRadius →
      ‖diskRelabelNeutralCLM finalCorrected‖ ≤ quadraticRadius →
      ‖diskPhysicalTransverseProjection firstCorrected‖ ≤ neutralWeight →
      ‖diskPhysicalTransverseProjection finalCorrected‖ ≤ neutralWeight →
      quadraticConstant * neutralWeight ≤ 1 / 2 →
      weightedProjectionDistance diskPhysicalTransverseProjection diskNeutralCLM neutralWeight first final ≤
        4 * (‖diskSpectralQuadraticObservable firstCorrected - diskSpectralQuadraticObservable finalCorrected‖ +
          neutralWeight * ‖diskNeutralCLM firstCorrected - diskNeutralCLM finalCorrected‖) := by
  obtain ⟨radius, positive, forcingRadius, forcingPositive, mapConstant, mapOne, inverse⟩ :=
    canonicalExteriorCommonRawSpectralCoordinate_exists_weighted_inverse_ball
  obtain ⟨quadraticRadius, quadraticPositive, quadraticConstant, quadraticOne, quadraticInverse⟩ :=
    diskSpectralQuadraticObservable_exists_weighted_inverse_ball
  refine ⟨radius, positive, forcingRadius, forcingPositive, mapConstant, mapOne,
    quadraticRadius, quadraticPositive, quadraticConstant, quadraticOne, ?_⟩
  intro count family index first final firstInside finalInside firstArea finalArea firstCentered finalCentered
    frequency time distance weight nonzero distancePositive weightNonnegative small separated weightBound forcingSmall
    neutralWeight neutralNonnegative neutralSmall mapSmall firstCorrected finalCorrected firstNeutral finalNeutral
    firstProjected finalProjected quadraticSmall
  have raw := inverse family index first final firstInside finalInside firstArea finalArea firstCentered finalCentered
    nonzero distancePositive weightNonnegative small separated weightBound forcingSmall
    neutralNonnegative neutralSmall mapSmall
  have quadratic := quadraticInverse firstCorrected finalCorrected firstNeutral finalNeutral neutralNonnegative
    firstProjected finalProjected quadraticSmall
  have scaled := mul_le_mul_of_nonneg_left quadratic (by norm_num : (0 : ℝ) ≤ 2)
  with_reducible_and_instances
    exact raw.trans (by simpa only [weightedProjectionDistance, map_sub, firstCorrected, finalCorrected,
      ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using scaled)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
