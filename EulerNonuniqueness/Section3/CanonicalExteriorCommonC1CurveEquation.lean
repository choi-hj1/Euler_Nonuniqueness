import EulerNonuniqueness.Section3.CanonicalExteriorCommonRawMaterialEquation
import EulerNonuniqueness.Section3.DiskActualAngularJetNeighborhood

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

local instance commonC1CurveEquationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

open EulerNonuniqueness.Section6

theorem canonicalExteriorCommonPhysicalCoordinate_exists_actual_C1_equation_radius :
    ∃ radius > 0, ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
      (curve velocity : ℝ → PeriodicC1HolderHalf) {frequency left right time distance weight mass : ℝ},
      Continuous curve → Continuous velocity → frequency ≠ 0 → ∀ (member : time ∈ Ioo left right),
      (∀ current ∈ Ioo left right, HasDerivAt curve (velocity current) current) →
      ‖curve time - standardCircleBanach‖ < radius →
      ∀ (positive : 0 < distance), 0 ≤ weight → 0 ≤ mass →
      ∀ (small : 192 * (family.patch index).radius ≤ distance),
      (∀ current ∈ Ioo left right, ∀ source, current ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
      (∀ current ∈ Ioo left right, ∀ source label,
        (family.patch source).boundaryVelocity current label =
          biotSavart (family.vorticity current) ((family.patch source).boundary current label)) →
      (∀ current ∈ Ioo left right, (family.patch index).center =ᶠ[𝓝 current] (family.patch index).centroid) →
      ∀ (centerGaps : ∀ current ∈ Ioo left right, ∀ source ∈ Finset.univ.erase index,
        distance + 3 * (family.patch source).radius ≤
          ‖(family.patch index).center current - (family.patch source).center current‖),
      (∀ current ∈ Ioo left right, (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) current) ((family.patch index).center current) position) ≤ weight) →
      (∀ current ∈ Ioo left right, (∫ position, |family.patchVorticity current index position|) ≤ mass) →
      ∃ angularSmall : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate (curve time))‖ < 1 / 2,
      HasDerivAt (fun current => family.canonicalExteriorCommonPhysicalCoordinate index frequency current (curve current))
        (frequency • diskEulerRotatingField (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time)) +
          family.canonicalExteriorCommonMaterialResidual index frequency time distance positive
            (by linarith [(family.patch index).radius_positive])
            (family.exterior_domain_gap_of_center_gaps index (centerGaps time member)) (curve time) angularSmall +
          family.canonicalExteriorCommonPhysicalDerivative index frequency time (curve time)
            (velocity time - frequency • diskEulerRotatingField (curve time) -
              family.canonicalProjectedExteriorContourField index time distance positive
                (by linarith [(family.patch index).radius_positive])
                (family.exterior_domain_gap_of_center_gaps index (centerGaps time member))
                (Circle.exp (frequency * time / 2)) (curve time))) time := by
  obtain ⟨radius, positiveRadius, jets⟩ := diskPhysicalSpectralCoordinate_exists_actual_angular_jet_neighborhood
  refine ⟨radius, positiveRadius, ?_⟩
  intro count family index curve velocity frequency left right time distance weight mass curveContinuous velocityContinuous
    nonzero member equation small positive weightNonnegative massNonnegative scale sourceInside material centered centerGaps weightBound massBound
  obtain ⟨angularSmall, nearby, cutoff, regular, nextLeft, nextRight, speed, nextMember, contained,
    inverseActual, _, baseBounds⟩ := jets curve velocity curveContinuous velocityContinuous member equation small
  let finalForce : ℝ → PeriodicC1HolderHalf := fun current => velocity current - frequency • diskEulerRotatingField (curve current)
  have velocityIdentity (current : ℝ) : frequency • diskEulerRotatingField (curve current) + finalForce current = velocity current := by
    dsimp only [finalForce]
    abel
  have curveEquation (current : ℝ) (inside : current ∈ Ioo nextLeft nextRight) :
      HasDerivAt curve (frequency • diskEulerRotatingField (curve current) + finalForce current) current := by
    rw [velocityIdentity]
    exact equation current (contained inside)
  have nextSourceInside (current : ℝ) (inside : current ∈ Ioo nextLeft nextRight) := sourceInside current (contained inside)
  have nextMaterial (current : ℝ) (inside : current ∈ Ioo nextLeft nextRight) := material current (contained inside)
  have nextCentered (current : ℝ) (inside : current ∈ Ioo nextLeft nextRight) := centered current (contained inside)
  have nextGaps (current : ℝ) (inside : current ∈ Ioo nextLeft nextRight) := centerGaps current (contained inside)
  have nextWeights (current : ℝ) (inside : current ∈ Ioo nextLeft nextRight) := weightBound current (contained inside)
  have nextMasses (current : ℝ) (inside : current ∈ Ioo nextLeft nextRight) := massBound current (contained inside)
  have actual := by
    with_reducible_and_instances
      exact family.canonicalExteriorCommonPhysicalCoordinate_hasDerivAt_material_raw index curve finalForce
        (frequency := frequency) (left := nextLeft) (right := nextRight) (time := time)
        (distance := distance) (weight := weight) (mass := mass) (speed := speed)
        nonzero nextMember angularSmall nearby cutoff regular curveEquation inverseActual
        (fun current inside => by simpa only [velocityIdentity] using baseBounds current inside)
        positive weightNonnegative massNonnegative scale nextSourceInside nextMaterial nextCentered nextGaps nextWeights nextMasses
  refine ⟨angularSmall, ?_⟩
  with_reducible_and_instances
    simpa only [finalForce] using actual

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
