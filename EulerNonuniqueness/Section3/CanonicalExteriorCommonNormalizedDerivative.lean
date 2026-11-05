import EulerNonuniqueness.Section3.CanonicalExteriorCommonPhysicalDerivative
import EulerNonuniqueness.Section3.DiskNormalizedSpectralRelativeError

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

def canonicalExteriorCommonNormalizedPhysicalCoordinate {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time : ℝ) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskNormalizedSpectralCoordinate (family.canonicalExteriorCommonPhysicalCoordinate index frequency time data)

def canonicalExteriorCommonNormalizedPhysicalDerivative {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time : ℝ) (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (diskPhysicalSpectralInverseDerivative (contourAreaCentroidNormalization
      (family.canonicalExteriorCommonPhysicalCoordinate index frequency time data))).comp
    ((fderiv ℝ contourAreaCentroidNormalization
      (family.canonicalExteriorCommonPhysicalCoordinate index frequency time data)).comp
      (family.canonicalExteriorCommonPhysicalDerivative index frequency time data))

theorem canonicalExteriorCommonNormalizedPhysicalCoordinate_hasFDerivAt {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (frequency time : ℝ)
    (data : PeriodicC1HolderHalf)
    (physicalActual : HasFDerivAt (family.canonicalExteriorCommonPhysicalCoordinate index frequency time)
      (family.canonicalExteriorCommonPhysicalDerivative index frequency time data) data)
    (nearby : ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time data - standardCircleBanach‖ < 1 / 3)
    (inverseActual : HasFDerivAt diskPhysicalSpectralCoordinate
      (diskPhysicalSpectralInverseDerivative (contourAreaCentroidNormalization
        (family.canonicalExteriorCommonPhysicalCoordinate index frequency time data)))
      (contourAreaCentroidNormalization (family.canonicalExteriorCommonPhysicalCoordinate index frequency time data))) :
    HasFDerivAt (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time)
      (family.canonicalExteriorCommonNormalizedPhysicalDerivative index frequency time data) data := by
  have normalizationActual := (contourAreaCentroidNormalization_differentiableAt _ nearby).hasFDerivAt
  have normalizedActual := normalizationActual.comp data physicalActual
  have actual := inverseActual.comp data normalizedActual
  simpa only [canonicalExteriorCommonNormalizedPhysicalCoordinate, diskNormalizedSpectralCoordinate,
    canonicalExteriorCommonNormalizedPhysicalDerivative, Function.comp_def] using actual

theorem canonicalExteriorCommonNormalizedPhysicalDerivative_apply {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (frequency time : ℝ)
    (data source : PeriodicC1HolderHalf) :
    family.canonicalExteriorCommonNormalizedPhysicalDerivative index frequency time data source =
      diskNormalizedSpectralError (family.canonicalExteriorCommonPhysicalCoordinate index frequency time data)
        (family.canonicalExteriorCommonPhysicalDerivative index frequency time data source) := rfl

theorem canonicalExteriorCommonNormalizedPhysicalDerivative_exists_relative_source_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count) (frequency time : ℝ)
        (first final firstSource finalSource : PeriodicC1HolderHalf),
      ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time first - standardCircleBanach‖ ≤ radius →
      ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time final - standardCircleBanach‖ ≤ radius →
      ‖family.canonicalExteriorCommonNormalizedPhysicalDerivative index frequency time first firstSource -
        family.canonicalExteriorCommonNormalizedPhysicalDerivative index frequency time final finalSource‖ ≤
      constant *
        (‖family.canonicalExteriorCommonPhysicalDerivative index frequency time first firstSource -
            family.canonicalExteriorCommonPhysicalDerivative index frequency time final finalSource‖ +
          ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time first -
            family.canonicalExteriorCommonPhysicalCoordinate index frequency time final‖ *
            ‖family.canonicalExteriorCommonPhysicalDerivative index frequency time final finalSource‖) := by
  obtain ⟨radius, positive, constant, one, relative⟩ := diskNormalizedSpectralError_exists_relative_ball
  refine ⟨radius, positive, constant, one, ?_⟩
  intro count family index frequency time first final firstSource finalSource firstInside finalInside
  exact relative _ _ _ _ firstInside finalInside

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
