import EulerNonuniqueness.Section3.CanonicalExteriorCommonRawCoordinateComparison

noncomputable section

open Metric Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6 EulerNonuniqueness.General

theorem canonicalExteriorCommonRawSpectralCoordinate_exists_weighted_inverse_ball :
    ∃ radius > 0, ∃ forcingRadius > 0, ∃ constant ≥ 1,
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
        (constant * (weight / |frequency|)) ≤ neutralWeight / 2 →
      weightedProjectionDistance diskPhysicalTransverseProjection diskNeutralCLM neutralWeight first final ≤
        2 * weightedProjectionDistance diskPhysicalTransverseProjection diskNeutralCLM neutralWeight
          (family.canonicalExteriorCommonRawSpectralCoordinate index frequency time first)
          (family.canonicalExteriorCommonRawSpectralCoordinate index frequency time final) := by
  obtain ⟨radius, positive, forcingRadius, forcingPositive, constant, one, relative⟩ :=
    canonicalExteriorCommonRawSpectralCoordinate_exists_relative_identity_ball
  refine ⟨radius, positive, forcingRadius, forcingPositive, constant, one, ?_⟩
  intro count family index first final firstInside finalInside firstArea finalArea firstCentered finalCentered
    frequency time distance weight nonzero distancePositive weightNonnegative small separated weightBound forcingSmall
    neutralWeight neutralNonnegative neutralSmall absorb
  have correction := relative family index first final firstInside finalInside firstArea finalArea firstCentered finalCentered
    nonzero distancePositive weightNonnegative small separated weightBound forcingSmall
  have correctionActual :
      ‖(family.canonicalExteriorCommonRawSpectralCoordinate index frequency time first - first) -
        (family.canonicalExteriorCommonRawSpectralCoordinate index frequency time final - final)‖ ≤
      (constant * (weight / |frequency|)) *
        (‖diskPhysicalTransverseProjection (first - final)‖ + ‖diskNeutralCLM (first - final)‖) := by
    simpa only [map_sub] using correction
  exact weightedProjectionDistance_common_coordinate_inverse
    diskPhysicalTransverseProjection diskNeutralCLM first final
    (family.canonicalExteriorCommonRawSpectralCoordinate index frequency time first)
    (family.canonicalExteriorCommonRawSpectralCoordinate index frequency time final)
    neutralNonnegative neutralSmall (by positivity) absorb correctionActual

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
