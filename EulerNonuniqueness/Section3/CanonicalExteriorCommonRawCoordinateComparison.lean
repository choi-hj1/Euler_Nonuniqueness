import EulerNonuniqueness.Section3.CanonicalExteriorCommonNormalizedShift
import EulerNonuniqueness.Section3.MovingStrainSpectralRelabelDomain
import EulerNonuniqueness.Section3.DiskSpectralRelativeStateBound
import EulerNonuniqueness.Section3.DiskNeutralIdentification
import EulerNonuniqueness.General.CommonCoordinateWeightedInverse

noncomputable section

open Filter Metric Set MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

open EulerNonuniqueness.Section6

def canonicalExteriorCommonRawSpectralCoordinate {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time : ℝ) (state : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  family.canonicalExteriorCommonNormalizedCoordinate index (diskNeutralCLM state) frequency time
    (diskPhysicalSpectralChart state)

theorem canonicalExteriorCommonRawSpectralCoordinate_exists_relative_identity_ball :
    ∃ radius > 0, ∃ forcingRadius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (first final : PeriodicC1HolderHalf), first ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea first = Real.pi → diskSpectralTubularArea final = Real.pi →
      contourCentroidFunctional (diskPhysicalSpectralChart first) = 0 →
      contourCentroidFunctional (diskPhysicalSpectralChart final) = 0 →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      48 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      weight / |frequency| ≤ forcingRadius →
      ‖(family.canonicalExteriorCommonRawSpectralCoordinate index frequency time first - first) -
        (family.canonicalExteriorCommonRawSpectralCoordinate index frequency time final - final)‖ ≤
      constant * (weight / |frequency|) *
        (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
          ‖diskNeutralCLM first - diskNeutralCLM final‖) := by
  obtain ⟨commonRadius, commonPositive, commonConstant, commonOne, common⟩ :=
    canonicalExteriorCommonNormalizedCoordinate_exists_relative_shift_ball
  obtain ⟨nearRadius, nearPositive, nearConstant, nearOne, near⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_near_identity_bound
  obtain ⟨chartRadius, chartPositive, chartConstant, chartOne, chartAbsolute, chartDifference⟩ :=
    diskPhysicalSpectralChart_exists_uniform_firstOrder_bounds
  obtain ⟨stateRadius, statePositive, stateConstant, stateNonnegative, stateDifference⟩ :=
    diskSpectralTubularArea_exists_relative_state_bound
  obtain ⟨inverseRadius, inversePositive, inverse⟩ := diskNormalizedSpectralCoordinate_exists_constraints_left_inverse
  obtain ⟨domainRadius, domainPositive, domain⟩ := movingStrainSpectral_exists_relabel_domain (by norm_num : (0 : ℝ) < 1)
  let angularRadius := min commonRadius nearRadius
  let radius := min chartRadius (min stateRadius (min inverseRadius (min domainRadius
    (min (angularRadius / (1 + ‖diskNeutralCLM‖)) (commonRadius / (8 * chartConstant))))))
  let forcingRadius := commonRadius / (16 * nearConstant)
  let geometryConstant := chartConstant * stateConstant * (1 + ‖diskMaterialNeutralEmbeddingCLM‖)
  let constant := commonConstant * (geometryConstant + 1)
  have chartNonnegative : 0 ≤ chartConstant := le_trans (by norm_num) chartOne
  have nearNonnegative : 0 ≤ nearConstant := le_trans (by norm_num) nearOne
  have geometryNonnegative : 0 ≤ geometryConstant := by dsimp [geometryConstant]; positivity
  have constantOne : 1 ≤ constant := by
    have productNonnegative : 0 ≤ commonConstant * geometryConstant := by positivity
    dsimp [constant]
    nlinarith
  have chartLe : radius ≤ chartRadius := min_le_left _ _
  have stateLe : radius ≤ stateRadius := (min_le_right _ _).trans (min_le_left _ _)
  have inverseLe : radius ≤ inverseRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have domainLe : radius ≤ domainRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have angularLe : radius ≤ angularRadius / (1 + ‖diskNeutralCLM‖) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have physicalLe : radius ≤ commonRadius / (8 * chartConstant) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨radius, by dsimp [radius, angularRadius]; positivity, forcingRadius,
    by dsimp [forcingRadius]; positivity, constant, constantOne, ?_⟩
  intro count family index first final firstInside finalInside firstArea finalArea firstCentered finalCentered
    frequency time distance weight nonzero positive weightNonnegative small separated weightBound forcingSmall
  have normSmall {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 radius) : ‖state‖ < radius := by
    simpa only [mem_ball, dist_zero_right] using inside
  have restrict {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 radius) {outer : ℝ}
      (ordered : radius ≤ outer) : state ∈ ball 0 outer := ball_subset_ball ordered inside
  have firstDomain := domain first (restrict firstInside domainLe)
  have finalDomain := domain final (restrict finalInside domainLe)
  have angularBound {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 radius) : ‖diskNeutralCLM state‖ ≤ angularRadius := by
    have stateBound := (normSmall inside).le.trans angularLe
    have product := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskNeutralCLM‖)).mp stateBound
    have projection := diskNeutralCLM.le_opNorm state
    nlinarith [norm_nonneg state]
  have physicalBound {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 radius) :
      ‖diskPhysicalSpectralChart state - standardCircleBanach‖ ≤ commonRadius / 8 := by
    have raw := (chartAbsolute state ((normSmall inside).le.trans chartLe)).1
    have stateBound := (normSmall inside).le.trans physicalLe
    have product := (le_div_iff₀ (by positivity : 0 < 8 * chartConstant)).mp stateBound
    nlinarith
  have firstDefect : ‖diskPhysicalSpectralChart first - diskRelabelCurve (diskNeutralCLM first) 1‖ ≤ 1 := by
    have base := movingStrainSpectral_stationary_base_eq_fixedRelabel first firstDomain.1
    rw [fixedRelabelEquivalence_circle _ firstDomain.1 (diskNeutralCLM_real first)] at base
    simpa only [diskPhysicalSpectralDefect, base] using firstDomain.2.2.2.le
  have finalDefect : ‖diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1‖ ≤ 1 := by
    have base := movingStrainSpectral_stationary_base_eq_fixedRelabel final finalDomain.1
    rw [fixedRelabelEquivalence_circle _ finalDomain.1 (diskNeutralCLM_real final)] at base
    simpa only [diskPhysicalSpectralDefect, base] using finalDomain.2.2.2.le
  have shiftBound {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 radius)
      (defect : ‖diskPhysicalSpectralChart state - diskRelabelCurve (diskNeutralCLM state) 1‖ ≤ 1) :
      ‖diskPhysicalSpectralChart state - family.canonicalExteriorAffineCoordinate index (diskNeutralCLM state)
        frequency time (diskPhysicalSpectralChart state)‖ ≤ commonRadius / 8 := by
    have raw := near family index (diskNeutralCLM state) ((angularBound inside).trans (min_le_right _ _))
      (diskNeutralCLM_real state) nonzero positive weightNonnegative
      (by linarith [(family.patch index).radius_positive]) separated weightBound (diskPhysicalSpectralChart state)
    rw [norm_sub_rev] at raw
    have factor : 0 ≤ weight / |frequency| := by positivity
    have scaled := mul_le_mul_of_nonneg_left (by linarith :
      1 + ‖diskPhysicalSpectralChart state - diskRelabelCurve (diskNeutralCLM state) 1‖ ≤ 2)
      (mul_nonneg nearNonnegative factor)
    have forcing : (weight / |frequency|) * (16 * nearConstant) ≤ commonRadius :=
      (le_div_iff₀ (by positivity : 0 < 16 * nearConstant)).mp forcingSmall
    exact raw.trans (by nlinarith)
  have firstShift := shiftBound firstInside firstDefect
  have finalShift := shiftBound finalInside finalDefect
  have actual := common family index (diskNeutralCLM first) (diskNeutralCLM final)
    (diskPhysicalSpectralChart first) (diskPhysicalSpectralChart final)
    ((angularBound firstInside).trans (min_le_left _ _)) ((angularBound finalInside).trans (min_le_left _ _))
    (diskNeutralCLM_real first) (diskNeutralCLM_real final) nonzero positive weightNonnegative small separated weightBound
    (by linarith [physicalBound firstInside]) (by linarith [physicalBound finalInside]) finalDefect
  have firstInverse := inverse first ((normSmall firstInside).trans_le inverseLe) firstArea firstCentered
  have finalInverse := inverse final ((normSmall finalInside).trans_le inverseLe) finalArea finalCentered
  rw [firstInverse, finalInverse] at actual
  have stateBound := stateDifference first final (restrict firstInside stateLe) (restrict finalInside stateLe) firstArea finalArea
  have embedding := diskRelabelNeutralCLM_difference_norm_le first final
  have stateBudget : ‖first - final‖ ≤ stateConstant * (1 + ‖diskMaterialNeutralEmbeddingCLM‖) *
      (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
        ‖diskNeutralCLM first - diskNeutralCLM final‖) := by
    have raw := stateBound.trans (mul_le_mul_of_nonneg_left (add_le_add_left embedding _) stateNonnegative)
    apply raw.trans
    have transverse := mul_le_mul_of_nonneg_right
      (by linarith [norm_nonneg diskMaterialNeutralEmbeddingCLM] : (1 : ℝ) ≤ 1 + ‖diskMaterialNeutralEmbeddingCLM‖)
      (norm_nonneg (diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final))
    have angular := mul_le_mul_of_nonneg_right
      (by linarith : ‖diskMaterialNeutralEmbeddingCLM‖ ≤ 1 + ‖diskMaterialNeutralEmbeddingCLM‖)
      (norm_nonneg (diskNeutralCLM first - diskNeutralCLM final))
    convert mul_le_mul_of_nonneg_left (add_le_add transverse angular) stateNonnegative using 1 <;> ring
  have physical := (chartDifference first final ((normSmall firstInside).le.trans chartLe)
    ((normSmall finalInside).le.trans chartLe)).1.trans (mul_le_mul_of_nonneg_left stateBudget chartNonnegative)
  have scalar := add_le_add_right physical ‖diskNeutralCLM first - diskNeutralCLM final‖
  have sumBound : ‖diskPhysicalSpectralChart first - diskPhysicalSpectralChart final‖ +
      ‖diskNeutralCLM first - diskNeutralCLM final‖ ≤
      (geometryConstant + 1) * (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
        ‖diskNeutralCLM first - diskNeutralCLM final‖) := by
    dsimp only [geometryConstant]
    nlinarith [norm_nonneg (diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final)]
  apply actual.trans
  exact (mul_le_mul_of_nonneg_left sumBound (by positivity : 0 ≤ commonConstant * (weight / |frequency|))).trans_eq
    (by dsimp only [constant]; ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
