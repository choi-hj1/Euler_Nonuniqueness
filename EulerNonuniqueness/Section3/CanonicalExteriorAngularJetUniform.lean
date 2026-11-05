import EulerNonuniqueness.Section3.CanonicalExteriorAngularJetRelative
import EulerNonuniqueness.Section3.RelabeledPrimitiveAngularUniform
import EulerNonuniqueness.Section3.MovingStrainRealUniform

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd

local instance angularJetUniformBilinearGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

local instance angularJetUniformBilinearModule : Module ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.module (R := ℝ) (R₃ := ℝ) (S₃ := ℝ) (M := PeriodicC1HolderHalf)
    (M₃ := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (σ₁₃ := RingHom.id ℝ)

local instance angularJetUniformBilinearSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem canonicalExteriorAffineAngularDerivative_exists_relative_weight96_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        {frequency : ℝ}, frequency ≠ 0 → ∀ time : ℝ,
      Summable (fun degree => (96 : ℝ) ^ (degree + 1) *
        ‖family.canonicalExteriorStaticCoefficient index time degree‖) →
      ∀ firstAngular finalAngular firstData finalData : PeriodicC1HolderHalf,
      ‖firstAngular‖ ≤ radius → ‖finalAngular‖ ≤ radius →
      ‖family.canonicalExteriorAffineAngularDerivative index firstAngular frequency time firstData -
        family.canonicalExteriorAffineAngularDerivative index finalAngular frequency time finalData‖ ≤
        constant * (((∑' degree, (96 : ℝ) ^ (degree + 1) *
          ‖family.canonicalExteriorStaticCoefficient index time degree‖) +
          ‖family.exteriorStrainModulatedCoefficient index frequency time‖) / |frequency|) *
          (‖firstData - finalData‖ +
            (1 + ‖finalData - diskRelabelCurve finalAngular 1‖) * ‖firstAngular - finalAngular‖) := by
  obtain ⟨primitiveRadius, primitivePositive, primitiveConstant, primitiveOne, primitives⟩ :=
    relabeledPrimitiveAngularDerivative_exists_uniform_weight96_ball
  obtain ⟨correctionRadius, correctionPositive, correctionConstant, correctionOne, correctionAbsolute, correctionRelative⟩ :=
    movingStrainRealCorrectionCLM_exists_uniform_relabel_bounds
  obtain ⟨jetRadius, jetPositive, jetConstant, jetOne, _, jetAbsolute, jetRelative⟩ :=
    movingStrainAngularCorrectionDerivative_exists_uniform_ball
  have regular : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun angular => diskRelabelCurve angular 1) (0 : PeriodicC1HolderHalf) :=
    EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt (diskRelabelMap_analyticAt 0)
  obtain ⟨baseRadius, basePositive, baseConstant, baseOne, _, baseAbsolute, baseRelative⟩ :=
    regular.exists_uniform_derivative_ball
  obtain ⟨valueRadius, valuePositive, valueConstant, _, valueRelative⟩ := diskRelabelMap_exists_uniform_lipschitz
  let radius := min primitiveRadius (min correctionRadius (min jetRadius (min baseRadius valueRadius)))
  let constant := primitiveConstant + jetConstant * (1 + (valueConstant : ℝ)) +
    2 * correctionConstant * baseConstant + 1
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ primitiveConstant + jetConstant * (1 + (valueConstant : ℝ)) +
        2 * correctionConstant * baseConstant := by positivity
    dsimp only [constant]
    linarith
  refine ⟨radius, by dsimp only [radius]; positivity, constant, constantOne, ?_⟩
  intro count family index frequency nonzero time weighted firstAngular finalAngular firstData finalData firstInside finalInside
  let scale := ((∑' degree, (96 : ℝ) ^ (degree + 1) *
    ‖family.canonicalExteriorStaticCoefficient index time degree‖) +
    ‖family.exteriorStrainModulatedCoefficient index frequency time‖) / |frequency|
  have sumNonnegative : 0 ≤ ∑' degree, (96 : ℝ) ^ (degree + 1) *
      ‖family.canonicalExteriorStaticCoefficient index time degree‖ := tsum_nonneg (fun degree => by positivity)
  have scaleNonnegative : 0 ≤ scale := by dsimp only [scale]; positivity
  have primitiveScale : (∑' degree, (96 : ℝ) ^ (degree + 1) *
      ‖family.canonicalExteriorStaticCoefficient index time degree‖) / |frequency| ≤ scale := by
    apply div_le_div_of_nonneg_right _ (abs_nonneg frequency)
    exact le_add_of_nonneg_right (norm_nonneg _)
  have strainScale : ‖family.exteriorStrainModulatedCoefficient index frequency time‖ / |frequency| ≤ scale := by
    apply div_le_div_of_nonneg_right _ (abs_nonneg frequency)
    exact le_add_of_nonneg_left sumNonnegative
  have within {angular : PeriodicC1HolderHalf} (inside : ‖angular‖ ≤ radius) :
      ‖angular‖ ≤ primitiveRadius ∧ ‖angular‖ ≤ correctionRadius ∧ ‖angular‖ ≤ jetRadius ∧
        ‖angular‖ ≤ baseRadius ∧ ‖angular‖ ≤ valueRadius := by
    dsimp only [radius] at inside
    exact ⟨inside.trans (min_le_left _ _), inside.trans ((min_le_right _ _).trans (min_le_left _ _)),
      inside.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))),
      inside.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))),
      inside.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))⟩
  have firstWithin := within firstInside
  have finalWithin := within finalInside
  have primitive := (primitives nonzero
    (fun degree current => family.canonicalExteriorStaticCoefficient index current degree) time weighted).2
      firstAngular finalAngular firstWithin.1 finalWithin.1
  have primitiveBound := primitive.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left primitiveScale (by linarith : 0 ≤ primitiveConstant)) (norm_nonneg _))
  have correctionBound : ‖family.exteriorStrainPhysicalCorrection index firstAngular frequency time‖ ≤
      correctionConstant * scale := by
    rw [exteriorStrainPhysicalCorrection, norm_smul, Real.norm_eq_abs, abs_inv]
    have actual := mul_le_mul_of_nonneg_left
      (correctionAbsolute firstAngular firstWithin.2.1
        (family.exteriorStrainModulatedCoefficient index frequency time)) (by positivity : 0 ≤ |frequency|⁻¹)
    have scalar := mul_le_mul_of_nonneg_left strainScale (by linarith : 0 ≤ correctionConstant)
    exact (actual.trans_eq (by ring)).trans scalar
  have correctionPair : ‖family.exteriorStrainPhysicalCorrection index firstAngular frequency time -
      family.exteriorStrainPhysicalCorrection index finalAngular frequency time‖ ≤
      correctionConstant * scale * ‖firstAngular - finalAngular‖ := by
    rw [exteriorStrainPhysicalCorrection, exteriorStrainPhysicalCorrection, ← smul_sub,
      norm_smul, Real.norm_eq_abs, abs_inv]
    have actual := mul_le_mul_of_nonneg_left
      (correctionRelative firstAngular finalAngular firstWithin.2.1 finalWithin.2.1
        (family.exteriorStrainModulatedCoefficient index frequency time)) (by positivity : 0 ≤ |frequency|⁻¹)
    have scalar := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left strainScale (by linarith : 0 ≤ correctionConstant)) (norm_nonneg (firstAngular - finalAngular))
    exact (actual.trans_eq (by ring)).trans scalar
  have jetBound : ‖frequency⁻¹ • movingStrainAngularCorrectionDerivative firstAngular
      (family.exteriorStrainModulatedCoefficient index frequency time)‖ ≤ jetConstant * scale := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro direction
    simp only [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_inv]
    have raw := (movingStrainAngularCorrectionDerivative firstAngular
      (family.exteriorStrainModulatedCoefficient index frequency time)).le_opNorm direction
    have bounded := raw.trans (mul_le_mul_of_nonneg_right
      (jetAbsolute firstAngular firstWithin.2.2.1 (family.exteriorStrainModulatedCoefficient index frequency time))
      (norm_nonneg direction))
    have actual := mul_le_mul_of_nonneg_left
      bounded
      (by positivity : 0 ≤ |frequency|⁻¹)
    have scalar := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left strainScale (by linarith : 0 ≤ jetConstant)) (norm_nonneg direction)
    exact (actual.trans_eq (by ring)).trans scalar
  have jetPair : ‖frequency⁻¹ • movingStrainAngularCorrectionDerivative firstAngular
      (family.exteriorStrainModulatedCoefficient index frequency time) - frequency⁻¹ •
      movingStrainAngularCorrectionDerivative finalAngular (family.exteriorStrainModulatedCoefficient index frequency time)‖ ≤
      jetConstant * scale * ‖firstAngular - finalAngular‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro direction
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv]
    have raw := EulerNonuniqueness.General.norm_operator_difference_apply_le
      (movingStrainAngularCorrectionDerivative firstAngular (family.exteriorStrainModulatedCoefficient index frequency time))
      (movingStrainAngularCorrectionDerivative finalAngular (family.exteriorStrainModulatedCoefficient index frequency time)) direction
    have bounded := raw.trans (mul_le_mul_of_nonneg_right
      (jetRelative firstAngular finalAngular firstWithin.2.2.1 finalWithin.2.2.1
        (family.exteriorStrainModulatedCoefficient index frequency time)) (norm_nonneg direction))
    have actual := mul_le_mul_of_nonneg_left
      bounded (by positivity : 0 ≤ |frequency|⁻¹)
    have scalar := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left strainScale (by linarith : 0 ≤ jetConstant)) (norm_nonneg (firstAngular - finalAngular)))
      (norm_nonneg direction)
    exact (actual.trans_eq (by ring)).trans scalar
  have baseBound := baseAbsolute finalAngular (by simpa only [sub_zero] using finalWithin.2.2.2.1)
  have basePair := baseRelative firstAngular finalAngular
    (by simpa only [sub_zero] using firstWithin.2.2.2.1)
    (by simpa only [sub_zero] using finalWithin.2.2.2.1)
  have valuePair := valueRelative firstAngular finalAngular firstWithin.2.2.2.2 finalWithin.2.2.2.2
  have incrementPair : ‖(firstData - diskRelabelCurve firstAngular 1) -
      (finalData - diskRelabelCurve finalAngular 1)‖ ≤
      ‖firstData - finalData‖ + (valueConstant : ℝ) * ‖firstAngular - finalAngular‖ := by
    have identity : (firstData - diskRelabelCurve firstAngular 1) - (finalData - diskRelabelCurve finalAngular 1) =
        (firstData - finalData) - (diskRelabelCurve firstAngular 1 - diskRelabelCurve finalAngular 1) := by abel
    rw [identity]
    exact (norm_sub_le _ _).trans (add_le_add_left valuePair _)
  have assembled := family.canonicalExteriorAffineAngularDerivative_relative_bound index
    firstAngular finalAngular firstData finalData frequency time
  dsimp only at assembled
  have bounded := assembled.trans (add_le_add (add_le_add primitiveBound
    (add_le_add (mul_le_mul jetBound incrementPair (norm_nonneg _) (by positivity))
      (mul_le_mul_of_nonneg_right jetPair (norm_nonneg _))))
    (add_le_add (mul_le_mul correctionBound basePair (norm_nonneg _) (by positivity))
      (mul_le_mul correctionPair baseBound (norm_nonneg _) (by positivity))))
  apply bounded.trans
  change _ ≤ constant * scale * _
  dsimp only [constant]
  have nonnegative : 0 ≤
      (primitiveConstant + jetConstant * (valueConstant : ℝ) + 2 * correctionConstant * baseConstant + 1) * scale *
        (‖firstData - finalData‖ + ‖finalData - diskRelabelCurve finalAngular 1‖ * ‖firstAngular - finalAngular‖) +
      (jetConstant + 1) * scale * ‖firstAngular - finalAngular‖ := by positivity
  nlinarith only [nonnegative]

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
