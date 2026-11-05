import EulerNonuniqueness.Section3.CanonicalExteriorNeutralSpeed
import EulerNonuniqueness.Section3.DiskNeutralIdentification

noncomputable section

open Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance trueAngularDriftBoundC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

open EulerNonuniqueness.Section6

theorem canonicalProjectedExteriorContourField_exists_true_angular_drift_bound_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (data : PeriodicC1HolderHalf), ‖data - standardCircleBanach‖ < radius →
      contourAreaFunctional data = Real.pi →
      ∀ (time distance weight frequency : ℝ) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
        (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖),
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      ∀ phase : Circle,
      ‖diskNeutralCLM (diskPhysicalSpectralInverseDerivative data
        (frequency • diskEulerRotatingField data + family.canonicalProjectedExteriorContourField index time distance positive
          (by linarith [(family.patch index).radius_positive]) separated phase data))‖ ≤
        constant * (|frequency| * ‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate data)‖ ^ 2 +
          weight * ‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate data)‖) := by
  obtain ⟨speedRadius, speedPositive, speedConstant, speedOne, speed⟩ :=
    canonicalProjectedExteriorContourField_exists_uniform_neutral_speed
  obtain ⟨coordinateRadius, coordinatePositive, coordinates⟩ :=
    diskPhysicalSpectralCoordinate_exists_radius speedPositive
  obtain ⟨inverseRadius, inversePositive, inverse⟩ := Metric.eventually_nhds_iff.mp
    diskPhysicalSpectralCoordinate_eventually_inverse_derivative
  let constant := ‖diskNeutralCLM‖ * speedConstant + 1
  have constantOne : 1 ≤ constant := by
    have productNonnegative : 0 ≤ ‖diskNeutralCLM‖ * speedConstant := by positivity
    dsimp only [constant]
    linarith
  refine ⟨min coordinateRadius inverseRadius, lt_min coordinatePositive inversePositive, constant, constantOne, ?_⟩
  intro count family index data nearby area time distance weight frequency positive weightNonnegative small
    separated weightBound phase
  obtain ⟨rightInverse, areaIdentity, tube, _⟩ := coordinates data (nearby.trans_le (min_le_left _ _))
  change diskPhysicalSpectralChart (diskPhysicalSpectralCoordinate data) = data at rightInverse
  have inverseActual := inverse (show dist data standardCircleBanach < inverseRadius by
    simpa only [dist_eq_norm] using nearby.trans_le (min_le_right _ _))
  have actualSpeed := speed family index time distance weight frequency positive weightNonnegative small separated weightBound phase
    (diskPhysicalSpectralCoordinate data) tube.le (areaIdentity.trans area)
  rw [rightInverse] at actualSpeed
  let neutralVelocity := frequency • diskRelabelNeutralCLM (diskSpectralTubularEulerField (diskPhysicalSpectralCoordinate data)) +
    diskRelabelNeutralCLM (diskPhysicalSpectralInverseDerivative data
      (family.canonicalProjectedExteriorContourField index time distance positive
        (by linarith [(family.patch index).radius_positive]) separated phase data))
  have identified : diskNeutralCLM neutralVelocity = diskNeutralCLM (diskPhysicalSpectralInverseDerivative data
      (frequency • diskEulerRotatingField data + family.canonicalProjectedExteriorContourField index time distance positive
        (by linarith [(family.patch index).radius_positive]) separated phase data)) := by
    simp only [neutralVelocity, map_add, map_smul, diskNeutralCLM_relabel_projection, inverseActual.2.2]
  rw [← identified]
  have angularBound := (diskNeutralCLM.le_opNorm neutralVelocity).trans
    (mul_le_mul_of_nonneg_left actualSpeed (norm_nonneg diskNeutralCLM))
  have coefficientLe : ‖diskNeutralCLM‖ * speedConstant ≤ constant := by dsimp only [constant]; linarith
  have scalar := mul_le_mul_of_nonneg_right coefficientLe (by positivity : 0 ≤
    |frequency| * ‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate data)‖ ^ 2 +
      weight * ‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate data)‖)
  exact (angularBound.trans_eq (by ring)).trans scalar

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
