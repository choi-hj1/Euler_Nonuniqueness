import EulerNonuniqueness.Section3.CanonicalExteriorAngularJetUniform
import EulerNonuniqueness.Section3.CanonicalExteriorWeight96Bound

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  angularJetUniformBilinearGroup angularJetUniformBilinearModule angularJetUniformBilinearSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorAffineAngularDerivative_exists_weight_bound_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular data : PeriodicC1HolderHalf), ‖angular‖ ≤ radius →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      192 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      ‖family.canonicalExteriorAffineAngularDerivative index angular frequency time data‖ ≤
        constant * (weight / |frequency|) * (1 + ‖data - diskRelabelCurve angular 1‖) := by
  obtain ⟨primitiveRadius, primitivePositive, primitiveConstant, primitiveOne, primitives⟩ :=
    relabeledPrimitiveAngularDerivative_exists_uniform_weight96_ball
  obtain ⟨correctionRadius, correctionPositive, correctionConstant, correctionOne, correctionAbsolute, _⟩ :=
    movingStrainRealCorrectionCLM_exists_uniform_relabel_bounds
  obtain ⟨jetRadius, jetPositive, jetConstant, jetOne, _, jetAbsolute, _⟩ :=
    movingStrainAngularCorrectionDerivative_exists_uniform_ball
  have regular : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun angular => diskRelabelCurve angular 1) (0 : PeriodicC1HolderHalf) :=
    EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt (diskRelabelMap_analyticAt 0)
  obtain ⟨baseRadius, basePositive, baseConstant, baseOne, _, baseAbsolute, _⟩ := regular.exists_uniform_derivative_ball
  let radius := min primitiveRadius (min correctionRadius (min jetRadius baseRadius))
  let constant := 96 * primitiveConstant / Real.pi + jetConstant / (2 * Real.pi) +
    correctionConstant * baseConstant / (2 * Real.pi) + 1
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ 96 * primitiveConstant / Real.pi + jetConstant / (2 * Real.pi) +
        correctionConstant * baseConstant / (2 * Real.pi) := by positivity
    dsimp only [constant]
    linarith
  refine ⟨radius, by dsimp only [radius]; positivity, constant, constantOne, ?_⟩
  intro count family index angular data angularInside frequency time distance weight nonzero positive weightNonnegative
    small separated weightBound
  have primitiveInside := angularInside.trans (min_le_left _ _)
  have correctionInside := angularInside.trans ((min_le_right _ _).trans (min_le_left _ _))
  have jetInside := angularInside.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have baseInside := angularInside.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have weighted := family.canonicalExteriorStaticCoefficient_summable_weight96 index time distance positive small separated
  have sumBound := family.canonicalExteriorStaticCoefficient_weight96_le index time distance weight positive
    weightNonnegative small separated weightBound
  have primitive := (primitives nonzero
    (fun degree current => family.canonicalExteriorStaticCoefficient index current degree) time weighted).1 angular primitiveInside
  have primitiveBound := primitive.trans (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right sumBound (abs_nonneg frequency)) (by linarith : 0 ≤ primitiveConstant))
  have strainBound : ‖family.exteriorStrainModulatedCoefficient index frequency time‖ ≤ weight / (2 * Real.pi) := by
    rw [exteriorStrainModulatedCoefficient, norm_mul, diskForcingPhase_norm, one_mul]
    exact family.exteriorTaylorCoefficient_one_norm_le index time distance weight positive separated weightBound
  have correctionBound : ‖family.exteriorStrainPhysicalCorrection index angular frequency time‖ ≤
      (correctionConstant / (2 * Real.pi)) * (weight / |frequency|) := by
    rw [exteriorStrainPhysicalCorrection, norm_smul, Real.norm_eq_abs, abs_inv]
    have raw := (correctionAbsolute angular correctionInside _).trans
      (mul_le_mul_of_nonneg_left strainBound (by linarith : 0 ≤ correctionConstant))
    exact (mul_le_mul_of_nonneg_left raw (by positivity)).trans_eq (by ring)
  have jetBound : ‖frequency⁻¹ • movingStrainAngularCorrectionDerivative angular
      (family.exteriorStrainModulatedCoefficient index frequency time)‖ ≤
      (jetConstant / (2 * Real.pi)) * (weight / |frequency|) := by
    have raw := (jetAbsolute angular jetInside _).trans
      (mul_le_mul_of_nonneg_left strainBound (by linarith : 0 ≤ jetConstant))
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro direction
    simp only [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_inv]
    have bounded := ((movingStrainAngularCorrectionDerivative angular
      (family.exteriorStrainModulatedCoefficient index frequency time)).le_opNorm direction).trans
        (mul_le_mul_of_nonneg_right raw (norm_nonneg direction))
    exact (mul_le_mul_of_nonneg_left bounded (by positivity : 0 ≤ |frequency|⁻¹)).trans_eq (by ring)
  have baseBound := baseAbsolute angular (by simpa only [sub_zero] using baseInside)
  let baseDerivative := fderiv ℝ (fun parameter => diskRelabelCurve parameter 1) angular
  have assembled := EulerNonuniqueness.General.movingAffineAngularJet_norm_le
    (relabeledPrimitiveAngularDerivative frequency
      (fun degree current => family.canonicalExteriorStaticCoefficient index current degree) time angular)
    (family.exteriorStrainPhysicalCorrection index angular frequency time) baseDerivative
    (frequency⁻¹ • movingStrainAngularCorrectionDerivative angular
      (family.exteriorStrainModulatedCoefficient index frequency time)) (data - diskRelabelCurve angular 1)
  have actual : ‖family.canonicalExteriorAffineAngularDerivative index angular frequency time data‖ ≤
      ‖relabeledPrimitiveAngularDerivative frequency
        (fun degree current => family.canonicalExteriorStaticCoefficient index current degree) time angular‖ +
      ‖frequency⁻¹ • movingStrainAngularCorrectionDerivative angular
        (family.exteriorStrainModulatedCoefficient index frequency time)‖ * ‖data - diskRelabelCurve angular 1‖ +
      ‖family.exteriorStrainPhysicalCorrection index angular frequency time‖ * ‖baseDerivative‖ := by
    with_reducible_and_instances
      convert (config := { transparency := .all }) assembled using 1
      all_goals first
        | (change (_ : TopologicalSpace PeriodicC1HolderHalf) = _; with_unfolding_all rfl)
        | (simp only [canonicalExteriorAffineAngularDerivative, canonicalExteriorStaticCoefficient, baseDerivative])
  have bounded := actual.trans (add_le_add (add_le_add primitiveBound
    (mul_le_mul_of_nonneg_right jetBound (norm_nonneg _)))
    (mul_le_mul correctionBound baseBound (norm_nonneg _) (by positivity)))
  apply bounded.trans
  dsimp only [constant]
  have nonnegative : 0 ≤ (96 * primitiveConstant / Real.pi + correctionConstant * baseConstant / (2 * Real.pi) + 1) *
      (weight / |frequency|) * ‖data - diskRelabelCurve angular 1‖ +
      (jetConstant / (2 * Real.pi) + 1) * (weight / |frequency|) := by positivity
  ring_nf at nonnegative ⊢
  linarith only [nonnegative]

theorem canonicalExteriorAffineAngularDerivative_exists_relative_weight_bound_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (firstAngular finalAngular firstData finalData : PeriodicC1HolderHalf),
      ‖firstAngular‖ ≤ radius → ‖finalAngular‖ ≤ radius →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      192 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      ‖family.canonicalExteriorAffineAngularDerivative index firstAngular frequency time firstData -
        family.canonicalExteriorAffineAngularDerivative index finalAngular frequency time finalData‖ ≤
        constant * (weight / |frequency|) *
          (‖firstData - finalData‖ +
            (1 + ‖finalData - diskRelabelCurve finalAngular 1‖) * ‖firstAngular - finalAngular‖) := by
  obtain ⟨radius, positive, coefficientConstant, coefficientOne, relative⟩ :=
    canonicalExteriorAffineAngularDerivative_exists_relative_weight96_ball
  let constant := coefficientConstant * (96 / Real.pi + 1 / (2 * Real.pi)) + 1
  have productNonnegative : 0 ≤ coefficientConstant * (96 / Real.pi + 1 / (2 * Real.pi)) := by positivity
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith
  refine ⟨radius, positive, constant, constantOne, ?_⟩
  intro count family index firstAngular finalAngular firstData finalData firstInside finalInside
    frequency time distance weight nonzero distancePositive weightNonnegative small separated weightBound
  have weighted := family.canonicalExteriorStaticCoefficient_summable_weight96 index time distance distancePositive small separated
  have sumBound := family.canonicalExteriorStaticCoefficient_weight96_le index time distance weight distancePositive
    weightNonnegative small separated weightBound
  have strainBound : ‖family.exteriorStrainModulatedCoefficient index frequency time‖ ≤ weight / (2 * Real.pi) := by
    rw [exteriorStrainModulatedCoefficient, norm_mul, diskForcingPhase_norm, one_mul]
    exact family.exteriorTaylorCoefficient_one_norm_le index time distance weight distancePositive separated weightBound
  have budget := div_le_div_of_nonneg_right (add_le_add sumBound strainBound) (abs_nonneg frequency)
  have actual := relative family index nonzero time weighted firstAngular finalAngular firstData finalData firstInside finalInside
  have enlarged := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left budget (by linarith : 0 ≤ coefficientConstant))
    (by positivity : 0 ≤ ‖firstData - finalData‖ +
      (1 + ‖finalData - diskRelabelCurve finalAngular 1‖) * ‖firstAngular - finalAngular‖)
  have coefficientLe : coefficientConstant * (96 / Real.pi + 1 / (2 * Real.pi)) ≤ constant := by
    dsimp only [constant]
    linarith
  have scalar := mul_le_mul_of_nonneg_right coefficientLe
    (by positivity : 0 ≤ (weight / |frequency|) *
      (‖firstData - finalData‖ + (1 + ‖finalData - diskRelabelCurve finalAngular 1‖) * ‖firstAngular - finalAngular‖))
  exact (actual.trans enlarged).trans ((by convert scalar using 1 <;> ring))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
