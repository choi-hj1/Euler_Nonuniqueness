import EulerNonuniqueness.Section3.CanonicalExteriorStaticRelativeAssembly
import EulerNonuniqueness.Section3.CanonicalExteriorAffinePhaseField

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  powerFirstJetOperatorGroup exteriorPowerSeriesOperatorSpace gaugeOperatorUniformSecondGroup

def canonicalExteriorStaticCoefficient {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (time : ℝ) (degree : ℕ) : ℂ :=
  family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
    (family.patch index).radius (degree + 1) time

def canonicalExteriorStaticPhaseResidual {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (angular : PeriodicC1HolderHalf) (frequency time distance : ℝ)
    (positive : 0 < distance) (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  family.canonicalExteriorAffinePhaseField index angular frequency time distance positive small separated data -
    frequency • diskEulerRotatingField (family.canonicalExteriorAffineCoordinate index angular frequency time data)

theorem canonicalExteriorHigherContourField_eq_static_series {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance : ℝ)
    (positive : 0 < distance) (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (phase : Circle) (increment : PeriodicC1HolderHalf) (nearby : ‖increment‖ < 1 / 3)
    (ratio : 24 * (family.patch index).radius / distance < 1)
    (weighted : Summable (fun degree => (24 : ℝ) ^ (degree + 1) *
      ‖family.canonicalExteriorStaticCoefficient index time degree‖)) :
    family.canonicalExteriorHigherContourField index time distance positive small separated phase
      (standardCircleBanach + increment) =
    circleBasedProjectedExteriorSeries phase
      (exteriorCoefficientWithoutLeading (family.canonicalExteriorStaticCoefficient index time)) increment := by
  have bounded : ‖standardCircleBanach + increment‖ ≤ 3 := by
    linarith [norm_add_le standardCircleBanach increment, standardCircleBanach_norm_bound]
  unfold canonicalExteriorHigherContourField
  rw [family.canonicalProjectedExteriorContourField_eq_series index time distance positive small separated
    phase increment nearby ratio]
  exact (circleBasedProjectedExteriorSeries_without_leading phase
    (family.canonicalExteriorStaticCoefficient index time) increment bounded weighted).symm

theorem canonicalExteriorStaticPhaseResidual_eq_staticResidual {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (nearby : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    {frequency time distance : ℝ} (nonzero : frequency ≠ 0) (positive : 0 < distance)
    (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (increment : PeriodicC1HolderHalf)
    (dataNearby : ‖diskRelabelCurve angular 1 - standardCircleBanach + increment‖ < 1 / 3)
    (ratio : 24 * (family.patch index).radius / distance < 1)
    (weighted : Summable (fun degree => (24 : ℝ) ^ (degree + 1) *
      ‖family.canonicalExteriorStaticCoefficient index time degree‖)) :
    family.canonicalExteriorStaticPhaseResidual index angular frequency time distance positive small separated
      (diskRelabelCurve angular 1 + increment) =
    canonicalExteriorStaticResidual (Circle.exp (frequency * time / 2)) frequency
      (family.canonicalExteriorStaticCoefficient index time) (diskRelabelCurve angular 1) increment
      ((diskRelabelCurve angular 1 + increment) -
        family.canonicalExteriorAffineCoordinate index angular frequency time (diskRelabelCurve angular 1 + increment))
      (family.relabeledExteriorHigherForcingPrimitive index angular frequency time)
      (family.exteriorStrainModulatedCoefficient index frequency time) := by
  have actual := family.canonicalExteriorAffinePhaseField_residual_identity index angular angularSmall realValues
    nearby nonzero positive small separated (diskRelabelCurve angular 1 + increment)
  dsimp only at actual
  have baseReconstruct : standardCircleBanach + (diskRelabelCurve angular 1 - standardCircleBanach) =
      diskRelabelCurve angular 1 := by abel
  have dataReconstruct : standardCircleBanach + (diskRelabelCurve angular 1 - standardCircleBanach + increment) =
      diskRelabelCurve angular 1 + increment := by abel
  have higherBase := family.canonicalExteriorHigherContourField_eq_static_series index time distance positive small
    separated (Circle.exp (frequency * time / 2)) (diskRelabelCurve angular 1 - standardCircleBanach)
    (nearby.trans_le (min_le_left _ _)) ratio weighted
  have higherData := family.canonicalExteriorHigherContourField_eq_static_series index time distance positive small
    separated (Circle.exp (frequency * time / 2))
    (diskRelabelCurve angular 1 - standardCircleBanach + increment) dataNearby ratio weighted
  have forceData := family.canonicalProjectedExteriorContourField_eq_series index time distance positive small
    separated (Circle.exp (frequency * time / 2))
    (diskRelabelCurve angular 1 - standardCircleBanach + increment) dataNearby ratio
  rw [baseReconstruct] at higherBase
  rw [dataReconstruct] at higherData forceData
  have displacement : family.relabeledExteriorForcingPrimitive index angular frequency time +
      family.exteriorStrainPhysicalCorrection index angular frequency time increment =
      (diskRelabelCurve angular 1 + increment) -
        family.canonicalExteriorAffineCoordinate index angular frequency time (diskRelabelCurve angular 1 + increment) := by
    unfold canonicalExteriorAffineCoordinate
    simp only [add_sub_cancel_left]
    abel
  simp only [add_sub_cancel_left] at actual
  rw [displacement, higherData, higherBase, forceData] at actual
  unfold canonicalExteriorStaticPhaseResidual canonicalExteriorStaticResidual diskRotatingShiftError
  rw [actual]
  have coefficientFunction : family.canonicalExteriorStaticCoefficient index time =
      (fun degree => family.exteriorTaylorCoefficient (Finset.univ.erase index)
        (family.patch index).center (family.patch index).radius (degree + 1) time) := rfl
  rw [coefficientFunction]
  simp only [sub_sub_cancel, exteriorStrainPhysicalCorrection, ContinuousLinearMap.smul_apply]

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
