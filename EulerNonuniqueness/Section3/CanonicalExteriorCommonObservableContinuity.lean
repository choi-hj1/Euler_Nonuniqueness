import EulerNonuniqueness.Section3.CanonicalExteriorCommonGeometricContinuity
import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundaryObservableEvolution

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

local instance commonObservableContinuityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem canonicalExteriorCommonCoordinates_exists_geometric_continuity_ball :
    ∃ rawRadius > 0, ∃ physicalRadius > 0, ∃ spectralRadius > 0,
    ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
      (curve : ℝ → PeriodicC1HolderHalf) {frequency time distance weight : ℝ},
    ContinuousAt curve time → ‖curve time - standardCircleBanach‖ ≤ rawRadius →
    frequency ≠ 0 → 0 < distance → 0 ≤ weight → 192 * (family.patch index).radius ≤ distance →
    (∀ source ∈ Finset.univ.erase index, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
    (∀ source ∈ Finset.univ.erase index, distance + 3 * (family.patch source).radius ≤
      ‖(family.patch index).center time - (family.patch source).center time‖) →
    (∀ᶠ current in 𝓝 time, (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) current) ((family.patch index).center current) position) ≤ weight) →
    ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time) - standardCircleBanach‖ ≤ physicalRadius →
    ‖family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (curve time)‖ ≤ spectralRadius →
    ContinuousAt (fun current => family.canonicalExteriorCommonQuadraticCoordinate index frequency current (curve current)) time ∧
    ContinuousAt (fun current => family.canonicalExteriorCommonTrueAngularCoordinate index frequency current (curve current)) time := by
  obtain ⟨angularRadius, angularPositive, affineContinuous⟩ :=
    canonicalExteriorAffineCoordinate_exists_moving_geometric_continuity
  obtain ⟨inverseRadius, inversePositive, _, _, inverseDifferentiable, _, _⟩ :=
    diskPhysicalSpectralCoordinate_hasLipschitzDerivativeNear_circle.exists_uniform_derivative_ball
  obtain ⟨physicalRadius, physicalPositive, _, _, normalizedDifferentiable, _, _⟩ :=
    diskNormalizedSpectralCoordinate_hasLipschitzDerivativeNear_circle.exists_uniform_derivative_ball
  obtain ⟨spectralRadius, spectralPositive, _, _, spectralDerivative, _⟩ :=
    diskSpectralQuadraticObservable_exists_uniform_derivative_ball
  have angularContinuous : ContinuousAt (fun data => diskNeutralCLM (diskPhysicalSpectralCoordinate data)) standardCircleBanach :=
    diskNeutralCLM.continuous.continuousAt.comp diskPhysicalSpectralCoordinate_continuousAt_circle
  have angularNear : ∀ᶠ data in 𝓝 standardCircleBanach, ‖diskNeutralCLM (diskPhysicalSpectralCoordinate data)‖ < angularRadius :=
    angularContinuous.norm.eventually (gt_mem_nhds (by simpa only [diskPhysicalSpectralCoordinate_circle, map_zero, norm_zero] using angularPositive))
  obtain ⟨angularPhysicalRadius, angularPhysicalPositive, angularSmall⟩ := Metric.eventually_nhds_iff.mp angularNear
  let rawRadius := min inverseRadius (angularPhysicalRadius / 2)
  refine ⟨rawRadius, lt_min inversePositive (by positivity), physicalRadius, physicalPositive, spectralRadius, spectralPositive, ?_⟩
  intro count family index curve frequency time distance weight curveContinuous curveSmall nonzero positive weightNonnegative scale
    inside gaps weightBound correctedSmall spectralSmall
  have inverseContinuous := (inverseDifferentiable (curve time) (curveSmall.trans (min_le_left _ _))).continuousAt
  have angularBound : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate (curve time))‖ < angularRadius := by
    apply angularSmall
    rw [dist_eq_norm]
    exact (curveSmall.trans (min_le_right _ _)).trans_lt (by linarith)
  have angularAlong : ContinuousAt (fun current => diskNeutralCLM (diskPhysicalSpectralCoordinate (curve current))) time :=
    diskNeutralCLM.continuous.continuousAt.comp (inverseContinuous.comp curveContinuous)
  have smallerScale : 48 * (family.patch index).radius ≤ distance := by linarith [(family.patch index).radius_positive]
  have physicalContinuous : ContinuousAt (fun current => family.canonicalExteriorCommonPhysicalCoordinate index frequency current (curve current)) time := by
    with_reducible_and_instances
      simpa only [canonicalExteriorCommonPhysicalCoordinate] using affineContinuous family index
        (fun current => diskNeutralCLM (diskPhysicalSpectralCoordinate (curve current))) curve angularBound
        angularAlong curveContinuous
        (Eventually.of_forall (fun _ => diskNeutralCLM_real _)) nonzero positive weightNonnegative
        smallerScale inside gaps weightBound
  have normalizedContinuous : ContinuousAt (fun current => family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency current (curve current)) time := by
    simpa only [canonicalExteriorCommonNormalizedPhysicalCoordinate, Function.comp_def] using
      ContinuousAt.comp (f := fun current => family.canonicalExteriorCommonPhysicalCoordinate index frequency current (curve current))
        (normalizedDifferentiable
          (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time)) correctedSmall).continuousAt physicalContinuous
  have quadraticContinuous := ContinuousAt.comp
    (f := fun current => family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency current (curve current))
    (spectralDerivative
      (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (curve time)) spectralSmall).1.continuousAt normalizedContinuous
  have neutralContinuous := ContinuousAt.comp
    (f := fun current => family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency current (curve current))
    diskNeutralCLM.continuous.continuousAt normalizedContinuous
  have result := And.intro quadraticContinuous neutralContinuous
  with_reducible_and_instances
    simpa only [canonicalExteriorCommonQuadraticCoordinate, canonicalExteriorCommonTrueAngularCoordinate, Function.comp_def]
      using result

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
