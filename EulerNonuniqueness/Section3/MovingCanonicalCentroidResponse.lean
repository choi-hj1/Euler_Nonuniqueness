import EulerNonuniqueness.Section3.ExteriorCentroidResponse
import EulerNonuniqueness.Section3.ExteriorGaugeContourSeries
import EulerNonuniqueness.Section3.MovingCanonicalExteriorForcing
import EulerNonuniqueness.Section3.ContourRotatingSelfMoments

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem FiniteMovingPatchFamily.canonicalExteriorContourForcing_centroid_derivative_eq_response
    {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance : ℝ)
    (positive : 0 < distance) (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (data : PeriodicC1HolderHalf) (bound : ‖data‖ ≤ 3) (phase : Circle)
    (nearby : ‖data - standardCircleBanach‖ < 1 / 3)
    (area : contourAreaFunctional data = Real.pi) (ratio : 24 * (family.patch index).radius / distance < 1) :
    fderiv ℝ contourCentroidFunctional data
      (family.canonicalExteriorContourForcing index time distance positive small separated data bound phase) =
      contourExteriorCentroidResponse phase
        (fun power => family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
          (family.patch index).radius (power + 1) time) data +
        (family.patch index).radius⁻¹ • ((phase : ℂ)⁻¹ *
          biotSavart (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time)) := by
  let source := family.canonicalExteriorSpatialContourField index time distance positive small separated
  have weighted : Summable (fun power => (24 : ℝ) ^ (power + 1) *
      ‖family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
        (family.patch index).radius (power + 1) time‖) := by
    simp_rw [family.exteriorTaylorCoefficient_eq_vorticityCoefficient (Finset.univ.erase index)
      (family.patch index).center (family.patch index).radius time _ positive separated]
    exact Section6.summable_exteriorVorticityCoefficient_weight
      (family.subfamilyVorticity_integrable (Finset.univ.erase index) time) _ (family.patch index).radius_positive.le
      positive (by norm_num) (family.subfamily_support_separated (Finset.univ.erase index)
        ((family.patch index).center time) time distance separated) ratio
  have series := family.exterior_general_contour_series_eq (Finset.univ.erase index) (family.patch index).center
    (family.patch index).radius time source rfl phase data bound (family.patch index).radius_positive positive separated ratio
  have derivativeConstant := DFunLike.congr_fun (contourCentroidFunctional_derivative_constant data nearby)
    ((family.patch index).radius⁻¹ • ((phase : ℂ)⁻¹ * source.field ((family.patch index).center time)))
  change (fderiv ℝ contourCentroidFunctional data) (c1Constant _) = _ at derivativeConstant
  change (fderiv ℝ contourCentroidFunctional data)
    (source.rotatedCompose data phase (family.patch index).radius_positive bound + c1Constant _) = _
  rw [map_add, derivativeConstant, series,
    ← contourExteriorCentroidResponse_eq_centroid_derivative phase _ data nearby bound area weighted]
  simp only [ContinuousLinearMap.id_apply]
  rw [show source.field = biotSavart (family.subfamilyVorticity (Finset.univ.erase index) time) from
    family.canonicalExteriorSpatialContourField_field index time distance positive small separated]

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}

theorem centerVelocity_eq_exterior_value_and_response
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialClock : initial.1 = 0)
    (initialCentered : ∀ index, contourCentroidFunctional (initial.2.2 index) = 0)
    (marginPositive : 0 < margin) {horizon time distance : ℝ}
    (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (nonnegativeTime : time ∈ Icc 0 horizon)
    (safe : ∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ)
    (index : Fin count) (positive : 0 < distance) (small : 8 * (trajectory.movingFamily.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (trajectory.movingFamily.patch source).domain time,
      distance ≤ ‖(trajectory.movingFamily.patch index).center time - position‖)
    (area : contourAreaFunctional ((trajectory.curve time).2.2 index) = Real.pi)
    (ratio : 24 * (trajectory.movingFamily.patch index).radius / distance < 1) :
    (trajectory.velocity time).2.1 index =
      biotSavart (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase index) time)
        ((trajectory.movingFamily.patch index).center time) +
      configuration.radius index • ((Circle.exp (configuration.density index * time / 2) : ℂ) *
        contourExteriorCentroidResponse (Circle.exp (configuration.density index * time / 2))
          (fun power => trajectory.movingFamily.exteriorTaylorCoefficient (Finset.univ.erase index)
            (trajectory.movingFamily.patch index).center (trajectory.movingFamily.patch index).radius (power + 1) time)
          ((trajectory.curve time).2.2 index)) := by
  let data := (trajectory.curve time).2.2 index
  let phase := Circle.exp (configuration.density index * time / 2)
  let response := contourExteriorCentroidResponse phase
    (fun power => trajectory.movingFamily.exteriorTaylorCoefficient (Finset.univ.erase index)
      (trajectory.movingFamily.patch index).center (trajectory.movingFamily.patch index).radius (power + 1) time) data
  let exteriorValue := biotSavart (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase index) time)
    ((trajectory.movingFamily.patch index).center time)
  have nearby : ‖data - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi)) :=
    ((trajectory.admissible time).2.1 index).trans_lt trajectory.shape_small
  have centered : contourCentroidFunctional data = 0 :=
    (trajectory.contourCentroid_conserved inside index).trans (initialCentered index)
  have bound : ‖data‖ ≤ 3 := configuration.movingStateAdmissible_shapes_bounded
    ((trajectory.shape_small.trans_le (min_le_left _ _)).le.trans (by norm_num)) (trajectory.admissible time) index
  have selfZero : fderiv ℝ contourCentroidFunctional data (diskEulerRotatingField data) = 0 := by
    rw [contourCentroidFunctional_derivative_raw_rotating_self data nearby, centered, mul_zero, smul_zero]
  have derivativeResponse := trajectory.movingFamily.canonicalExteriorContourForcing_centroid_derivative_eq_response
    index time distance positive small separated data bound phase (nearby.trans_le (min_le_left _ _)) area ratio
  rw [trajectory.velocity_eq_uncut_of_margin marginPositive time (safe time nonnegativeTime)]
  change configuration.radius index • ((configuration.movingStatePhase (trajectory.curve time) index : ℂ) *
    fderiv ℝ contourCentroidFunctional data (configuration.movingStateRawField (trajectory.curve time) index)) = _
  rw [configuration.movingStateRawField_self_external, map_add, map_smul, selfZero, smul_zero, zero_add,
    trajectory.movingStateExternalField_eq_canonical_of_margin initialClock marginPositive inside nonnegativeTime safe index positive small separated,
    trajectory.movingStatePhase_eq_density_time_of_margin initialClock marginPositive inside nonnegativeTime safe index,
    derivativeResponse]
  change configuration.radius index • ((phase : ℂ) * (response +
    (configuration.radius index)⁻¹ • ((phase : ℂ)⁻¹ * exteriorValue))) =
      exteriorValue + configuration.radius index • ((phase : ℂ) * response)
  simp only [Complex.real_smul, Complex.ofReal_inv]
  have phaseNonzero : (phase : ℂ) ≠ 0 := Circle.coe_ne_zero phase
  field_simp [(configuration.radius_pos index).ne', phaseNonzero] <;> ring

end MovingCentroidGaugeTrajectory

end EulerNonuniqueness.Paper
