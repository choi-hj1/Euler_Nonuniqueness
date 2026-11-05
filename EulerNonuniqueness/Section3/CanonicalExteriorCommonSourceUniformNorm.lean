import EulerNonuniqueness.Section3.CanonicalExteriorCommonQuadraticEvolution
import EulerNonuniqueness.Section3.CanonicalExteriorAngularJetWeightBound
import EulerNonuniqueness.Section3.CanonicalPhysicalCorrectionBound
import EulerNonuniqueness.Section3.DiskPhysicalSpectralFirstOrderBounds
import EulerNonuniqueness.Section3.MovingStrainSpectralRelabelDomain

noncomputable section

open Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorCommonPhysicalDerivative_exists_uniform_norm_ball :
    ∃ rawRadius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (state : PeriodicC1HolderHalf), state ∈ ball 0 rawRadius →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      192 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      weight / |frequency| ≤ 1 →
      ‖family.canonicalExteriorCommonPhysicalDerivative index frequency time (diskPhysicalSpectralChart state)‖ ≤ constant := by
  obtain ⟨correctionRadius, correctionPositive, correctionConstant, correctionOne, corrections⟩ :=
    exteriorStrainPhysicalCorrection_exists_uniform_norm_bound
  obtain ⟨angularRadius, angularPositive, angularConstant, angularOne, angulars⟩ :=
    canonicalExteriorAffineAngularDerivative_exists_weight_bound_ball
  obtain ⟨chartRadius, chartPositive, chartConstant, chartOne, charts, _⟩ :=
    diskPhysicalSpectralChart_exists_uniform_firstOrder_bounds
  obtain ⟨domainRadius, domainPositive, domains⟩ := movingStrainSpectral_exists_relabel_domain (by norm_num : (0 : ℝ) < 1)
  obtain ⟨inverseRadius, inversePositive, inverses⟩ := Metric.eventually_nhds_iff.mp diskPhysicalSpectralCoordinate_eventually_left_inverse
  let parameterRadius := min correctionRadius angularRadius
  let rawRadius := min chartRadius (min domainRadius (min inverseRadius (parameterRadius / (1 + ‖diskNeutralCLM‖))))
  let constant := 1 + correctionConstant + 2 * angularConstant * ‖diskNeutralCLM‖ * chartConstant
  have correctionNonnegative : 0 ≤ correctionConstant := by linarith
  have angularNonnegative : 0 ≤ angularConstant := by linarith
  have chartNonnegative : 0 ≤ chartConstant := by linarith
  have constantOne : 1 ≤ constant := by
    have productNonnegative : 0 ≤ 2 * angularConstant * ‖diskNeutralCLM‖ * chartConstant := by positivity
    dsimp only [constant]
    linarith
  refine ⟨rawRadius, by dsimp only [rawRadius, parameterRadius]; positivity, constant, constantOne, ?_⟩
  intro count family index state inside frequency time distance weight nonzero positive weightNonnegative small separated weightBound forcingSmall
  have stateSmall : ‖state‖ ≤ rawRadius := (by simpa only [mem_ball, dist_zero_right] using inside : ‖state‖ < rawRadius).le
  have domain := domains state (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) inside)
  have stateInverse : diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart state) = state := by
    apply inverses
    simpa only [mem_ball, dist_zero_right] using
      (ball_subset_ball ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) inside : state ∈ ball 0 inverseRadius)
  have base := movingStrainSpectral_stationary_base_eq_fixedRelabel state domain.1
  rw [fixedRelabelEquivalence_circle _ domain.1 (diskNeutralCLM_real state)] at base
  have defect : ‖diskPhysicalSpectralChart state - diskRelabelCurve (diskNeutralCLM state) 1‖ ≤ 1 := by
    simpa only [diskPhysicalSpectralDefect, base] using domain.2.2.2.le
  have parameterSmall : ‖diskNeutralCLM state‖ ≤ parameterRadius := by
    have scaled := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskNeutralCLM‖)).mp
      (stateSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    nlinarith [diskNeutralCLM.le_opNorm state, norm_nonneg state]
  have correction := corrections family index (diskNeutralCLM state) (parameterSmall.trans (min_le_left _ _))
    positive weightNonnegative separated weightBound (frequency := frequency) (time := time)
  have correctionBound := correction.trans (mul_le_mul_of_nonneg_left forcingSmall correctionNonnegative)
  simp only [mul_one] at correctionBound
  have angular := angulars family index (diskNeutralCLM state) (diskPhysicalSpectralChart state)
    (parameterSmall.trans (min_le_right _ _)) nonzero positive weightNonnegative small separated weightBound
  have angularBound : ‖family.canonicalExteriorAffineAngularDerivative index (diskNeutralCLM state) frequency time (diskPhysicalSpectralChart state)‖ ≤
      2 * angularConstant := by
    have bounded := angular.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left forcingSmall angularNonnegative) (show 1 + ‖diskPhysicalSpectralChart state - diskRelabelCurve (diskNeutralCLM state) 1‖ ≤ 2 by linarith)
      (by positivity) (by positivity))
    exact bounded.trans_eq (by ring)
  have inverseBound := (charts state (stateSmall.trans (min_le_left _ _))).2
  let jet := family.canonicalExteriorAffineAngularDerivative index (diskNeutralCLM state) frequency time (diskPhysicalSpectralChart state)
  let correctionOperator := family.exteriorStrainPhysicalCorrection index (diskNeutralCLM state) frequency time
  let inverseOperator := diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart state)
  have inner := (ContinuousLinearMap.opNorm_comp_le diskNeutralCLM inverseOperator).trans
    (mul_le_mul_of_nonneg_left inverseBound (norm_nonneg diskNeutralCLM))
  have outer := (ContinuousLinearMap.opNorm_comp_le jet (diskNeutralCLM.comp inverseOperator)).trans
    (mul_le_mul angularBound inner (norm_nonneg _) (by positivity))
  have identityBound := (norm_sub_le (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf) correctionOperator).trans
    (add_le_add (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := PeriodicC1HolderHalf)) correctionBound)
  have total := (norm_add_le (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf - correctionOperator)
    (jet.comp (diskNeutralCLM.comp inverseOperator))).trans (add_le_add identityBound outer)
  with_reducible_and_instances
    simpa only [canonicalExteriorCommonPhysicalDerivative, stateInverse, jet, correctionOperator, inverseOperator,
      constant, mul_assoc] using total

theorem canonicalExteriorCommonQuadraticSourceOperator_exists_uniform_norm_ball :
    ∃ rawRadius > 0, ∃ physicalRadius > 0, ∃ spectralRadius > 0, ∃ constant ≥ 1,
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
      ‖family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state)‖ ≤ spectralRadius →
      ‖family.canonicalExteriorCommonQuadraticSourceOperator index frequency time (diskPhysicalSpectralChart state)‖ ≤ constant := by
  obtain ⟨rawRadius, rawPositive, physicalConstant, physicalOne, physicals⟩ :=
    canonicalExteriorCommonPhysicalDerivative_exists_uniform_norm_ball
  obtain ⟨physicalRadius, physicalPositive, normalConstant, normalOne, normals⟩ :=
    canonicalExteriorCommonNormalizedPhysicalDerivative_exists_norm_ball
  obtain ⟨spectralRadius, spectralPositive, quadraticConstant, quadraticOne, quadratics, _⟩ :=
    diskSpectralQuadraticObservable_exists_uniform_derivative_ball
  let constant := quadraticConstant * normalConstant * physicalConstant
  have firstProduct : 1 ≤ quadraticConstant * normalConstant := by nlinarith
  have constantOne : 1 ≤ constant := by
    have scaled := mul_le_mul_of_nonneg_right firstProduct (by linarith : 0 ≤ physicalConstant)
    dsimp only [constant]
    nlinarith only [scaled, physicalOne]
  refine ⟨rawRadius, rawPositive, physicalRadius, physicalPositive, spectralRadius, spectralPositive, constant, constantOne, ?_⟩
  intro count family index state inside frequency time distance weight nonzero positive weightNonnegative small separated weightBound forcingSmall
    physicalInside spectralInside
  have physical := physicals family index state inside nonzero positive weightNonnegative small separated weightBound forcingSmall
  have normal := (normals family index frequency time (diskPhysicalSpectralChart state) physicalInside).trans
    (mul_le_mul_of_nonneg_left physical (by linarith : 0 ≤ normalConstant))
  have quadratic := (quadratics _ spectralInside).2
  have actual := (ContinuousLinearMap.opNorm_comp_le
    (fderiv ℝ diskSpectralQuadraticObservable
      (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state)))
    (family.canonicalExteriorCommonNormalizedPhysicalDerivative index frequency time (diskPhysicalSpectralChart state))).trans
      (mul_le_mul quadratic normal (norm_nonneg _) (by linarith : 0 ≤ quadraticConstant))
  exact actual.trans_eq (by dsimp only [constant]; ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
