import EulerNonuniqueness.Section3.CanonicalExteriorCommonSourceUniformNorm

noncomputable section

open Metric MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

def canonicalExteriorCommonTrueAngularSourceOperator {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time : ℝ) (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  diskNeutralCLM.comp (family.canonicalExteriorCommonNormalizedPhysicalDerivative index frequency time data)

theorem canonicalExteriorCommonTrueAngularSourceOperator_exists_uniform_norm_ball :
    ∃ rawRadius > 0, ∃ physicalRadius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (state : PeriodicC1HolderHalf), state ∈ ball 0 rawRadius →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      192 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      weight / |frequency| ≤ 1 →
      ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state) - standardCircleBanach‖ ≤ physicalRadius →
      ‖family.canonicalExteriorCommonTrueAngularSourceOperator index frequency time (diskPhysicalSpectralChart state)‖ ≤ constant := by
  obtain ⟨rawRadius, rawPositive, physicalConstant, physicalOne, physicals⟩ :=
    canonicalExteriorCommonPhysicalDerivative_exists_uniform_norm_ball
  obtain ⟨physicalRadius, physicalPositive, normalConstant, normalOne, normals⟩ :=
    canonicalExteriorCommonNormalizedPhysicalDerivative_exists_norm_ball
  let constant := ‖diskNeutralCLM‖ * normalConstant * physicalConstant + 1
  have physicalNonnegative : 0 ≤ physicalConstant := by linarith
  have normalNonnegative : 0 ≤ normalConstant := by linarith
  have productNonnegative : 0 ≤ ‖diskNeutralCLM‖ * normalConstant * physicalConstant := by positivity
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith
  refine ⟨rawRadius, rawPositive, physicalRadius, physicalPositive, constant, constantOne, ?_⟩
  intro count family index state inside frequency time distance weight nonzero positive weightNonnegative small separated weightBound forcingSmall physicalInside
  have physical := physicals family index state inside nonzero positive weightNonnegative small separated weightBound forcingSmall
  have normal := (normals family index frequency time (diskPhysicalSpectralChart state) physicalInside).trans
    (mul_le_mul_of_nonneg_left physical normalNonnegative)
  have actual := (ContinuousLinearMap.opNorm_comp_le diskNeutralCLM
    (family.canonicalExteriorCommonNormalizedPhysicalDerivative index frequency time (diskPhysicalSpectralChart state))).trans
      (mul_le_mul_of_nonneg_left normal (norm_nonneg diskNeutralCLM))
  have coefficientLe : ‖diskNeutralCLM‖ * normalConstant * physicalConstant ≤ constant := by dsimp only [constant]; linarith
  exact (actual.trans_eq (by ring)).trans coefficientLe

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
