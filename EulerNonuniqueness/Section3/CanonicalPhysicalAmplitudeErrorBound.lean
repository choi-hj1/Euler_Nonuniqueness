import EulerNonuniqueness.Section3.CanonicalPhysicalAmplitudeBound
import EulerNonuniqueness.Section3.RelabeledExteriorAmplitudeBound

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem exteriorAffineAmplitudeError_exists_uniform_value_bound :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular : PeriodicC1HolderHalf) (angularSmall : ‖angular‖ < 1 / 2), ‖angular‖ ≤ radius →
      ∀ {frequency time distance weight mass : ℝ}, frequency ≠ 0 →
      time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime →
      (∀ label, (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label)) →
      (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid →
      0 < distance → 0 ≤ weight → 0 ≤ mass → 8 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight →
      (∫ position, |family.patchVorticity time index position|) ≤ mass →
      ∀ direction : PeriodicC1HolderHalf,
      ‖fixedRelabelEquivalence angular angularSmall (family.exteriorAmplitudeDerivativePrimitive index frequency time) +
        family.exteriorStrainAmplitudeCorrection index angular frequency time direction‖ ≤
        constant * (weight ^ 2 + mass * weight / distance ^ 2) / |frequency| * (1 + ‖direction‖) := by
  obtain ⟨radius, positiveRadius, operatorConstant, operatorOne, operatorBounds⟩ :=
    exteriorStrainAmplitudeCorrection_exists_uniform_norm_bound
  let constant := operatorConstant + 1664 / Real.pi ^ 2 + 1
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ 1664 / Real.pi ^ 2 := by positivity
    dsimp [constant]
    linarith
  have operatorLe : operatorConstant ≤ constant := by
    have nonnegative : 0 ≤ 1664 / Real.pi ^ 2 := by positivity
    dsimp [constant]
    linarith
  have primitiveLe : 1664 / Real.pi ^ 2 ≤ constant := by dsimp [constant]; linarith
  have firstLe : 1472 / Real.pi ^ 2 ≤ constant :=
    (div_le_div_of_nonneg_right (by norm_num : (1472 : ℝ) ≤ 1664) (sq_nonneg Real.pi)).trans primitiveLe
  have secondLe : 192 / Real.pi ^ 2 ≤ constant :=
    (div_le_div_of_nonneg_right (by norm_num : (192 : ℝ) ≤ 1664) (sq_nonneg Real.pi)).trans primitiveLe
  refine ⟨radius, positiveRadius, constant, constantOne, ?_⟩
  intro count family index angular angularSmall angularNear frequency time distance weight mass nonzero inside material centered
    positive weightNonnegative massNonnegative small separated weightBound massBound direction
  have primitiveActual := family.relabeledExteriorAmplitudeDerivativePrimitive_norm_le index angular angularSmall nonzero
    inside material centered positive weightNonnegative massNonnegative small separated weightBound massBound
  have primitiveBound : ‖fixedRelabelEquivalence angular angularSmall
      (family.exteriorAmplitudeDerivativePrimitive index frequency time)‖ ≤
      constant * (weight ^ 2 + mass * weight / distance ^ 2) / |frequency| := by
    have numerical := add_le_add
      (mul_le_mul_of_nonneg_right firstLe (div_nonneg (sq_nonneg weight) (abs_nonneg frequency)))
      (mul_le_mul_of_nonneg_right secondLe (div_nonneg (mul_nonneg massNonnegative weightNonnegative)
        (mul_nonneg (sq_nonneg distance) (abs_nonneg frequency))))
    exact primitiveActual.trans (by convert numerical using 1 <;> ring)
  have operatorActual := operatorBounds family index angular angularNear inside material centered positive weightNonnegative
    massNonnegative small separated weightBound massBound (frequency := frequency)
  have operatorBound : ‖family.exteriorStrainAmplitudeCorrection index angular frequency time‖ ≤
      constant * (weight ^ 2 + mass * weight / distance ^ 2) / |frequency| :=
    operatorActual.trans (by
      have numerical := mul_le_mul_of_nonneg_right operatorLe
        (div_nonneg (show 0 ≤ weight ^ 2 + mass * weight / distance ^ 2 by positivity) (abs_nonneg frequency))
      convert numerical using 1 <;> ring)
  generalize primitiveEq : fixedRelabelEquivalence angular angularSmall
    (family.exteriorAmplitudeDerivativePrimitive index frequency time) = primitive at *
  generalize operatorEq : family.exteriorStrainAmplitudeCorrection index angular frequency time = operator at *
  have applied := (operator.le_opNorm direction).trans (mul_le_mul_of_nonneg_right operatorBound (norm_nonneg _))
  exact (norm_add_le _ _).trans ((add_le_add primitiveBound applied).trans_eq (by ring))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
