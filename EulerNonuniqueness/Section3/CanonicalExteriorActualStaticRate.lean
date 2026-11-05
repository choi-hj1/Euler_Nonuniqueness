import EulerNonuniqueness.Section3.CanonicalExteriorActualStaticScale
import EulerNonuniqueness.Section3.DiskNeutralContinuousVectors
import EulerNonuniqueness.Section3.RelabeledPrimitiveContinuousVectors

noncomputable section

open Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorStaticPhaseResidual_exists_actual_quadratic_rate_ball :
    ∃ rawRadius > 0, ∃ forcingRadius > 0, ∃ shapeRadius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (first final : PeriodicC1HolderHalf), first ∈ ball 0 rawRadius → final ∈ ball 0 rawRadius →
      first ∈ contourContinuousVectorSubmodule → final ∈ contourContinuousVectorSubmodule →
      diskPhysicalSpectralChart first ∈ contourContinuousVectorSubmodule →
      diskPhysicalSpectralChart final ∈ contourContinuousVectorSubmodule →
      diskSpectralTubularArea first = Real.pi → diskSpectralTubularArea final = Real.pi →
      contourCentroidFunctional (diskPhysicalSpectralChart first) = 0 →
      contourCentroidFunctional (diskPhysicalSpectralChart final) = 0 →
      ∀ {frequency time distance weight radius : ℝ}, frequency ≠ 0 →
      ∀ (positive : 0 < distance) (weightNonnegative : 0 ≤ weight),
      0 ≤ radius → radius ≤ shapeRadius →
      ‖diskPhysicalTransverseProjection first‖ ≤ radius → ‖diskPhysicalTransverseProjection final‖ ≤ radius →
      ∀ (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖),
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      weight / |frequency| ≤ forcingRadius → weight / |frequency| ≤ radius →
      (weight / |frequency|) ^ 2 ≤ radius ^ 3 →
      (weight / |frequency|) * ((family.patch index).radius / distance) ≤ radius ^ 2 →
      ‖family.canonicalExteriorStaticPhaseResidual index (diskNeutralCLM first) frequency time distance positive
          (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart first) -
        family.canonicalExteriorStaticPhaseResidual index (diskNeutralCLM final) frequency time distance positive
          (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart final)‖ ≤
        constant * |frequency| * radius ^ 2 *
          (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
            radius * ‖diskNeutralCLM first - diskNeutralCLM final‖) := by
  obtain ⟨scaleRadius, scalePositive, scaleConstant, scaleOne, scales⟩ :=
    canonicalExteriorStaticRelativeBudget_exists_actual_scale_ball
  obtain ⟨assemblyRadius, assemblyPositive, assemblyConstant, assemblyNonnegative, assembly⟩ :=
    canonicalExteriorStaticPhaseResidual_exists_pair_relative_ball
  obtain ⟨geometryRadius, geometryPositive, geometryConstant, geometryOne, geometry⟩ :=
    diskPhysicalSpectralChart_exists_true_angular_pair_bounds
  obtain ⟨shiftRadius, shiftPositive, shiftConstant, shiftOne, shifts⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_near_identity_bound
  have circle : diskRelabelCurve (0 : PeriodicC1HolderHalf) 1 = standardCircleBanach := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rw [diskRelabelCurve_value]
    change Complex.exp ((1 : ℂ) * (Complex.I * 0)) * standardCircle label = standardCircle label
    simp
  let threshold := min (assemblyRadius / 4) (min (1 / 3) (min 1 (2 / (3 * Real.pi))))
  have thresholdPositive : 0 < threshold := by dsimp only [threshold]; positivity
  have baseSmall : ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskRelabelCurve (diskNeutralCLM state) 1 - standardCircleBanach‖ < threshold := by
    have relabelContinuous : ContinuousAt (fun state => diskRelabelCurve (diskNeutralCLM state) 1) (0 : PeriodicC1HolderHalf) :=
      ContinuousAt.comp (g := fun angular => diskRelabelCurve angular 1) (f := fun state => diskNeutralCLM state)
        (diskRelabelMap_analyticAt _).continuousAt diskNeutralCLM.continuous.continuousAt
    have continuous : ContinuousAt (fun state => diskRelabelCurve (diskNeutralCLM state) 1 - standardCircleBanach)
        (0 : PeriodicC1HolderHalf) := relabelContinuous.sub continuousAt_const
    apply continuous.norm.eventually (gt_mem_nhds ?_)
    simpa only [map_zero, circle, sub_self, norm_zero] using thresholdPositive
  obtain ⟨baseRadius, basePositive, bases⟩ := Metric.eventually_nhds_iff.mp baseSmall
  let angularRadius := min shiftRadius (1 / 4)
  let rawRadius := min scaleRadius (min geometryRadius (min baseRadius (angularRadius / (1 + ‖diskNeutralCLM‖))))
  let forcingRadius := assemblyRadius / (8 * shiftConstant * (1 + geometryConstant))
  let shapeRadius := min 1 (assemblyRadius / (8 * geometryConstant))
  let polynomial := 5 * scaleConstant ^ 2 + 10 * scaleConstant ^ 3 + 4 * scaleConstant ^ 4 + 1
  let constant := assemblyConstant * 3 * polynomial + 1
  have geometryPositiveConstant : 0 < geometryConstant := by linarith
  have shiftPositiveConstant : 0 < shiftConstant := by linarith
  have scaleNonnegative : 0 ≤ scaleConstant := by linarith
  have polynomialPositive : 0 < polynomial := by dsimp only [polynomial]; positivity
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ assemblyConstant * 3 * polynomial := by positivity
    dsimp only [constant]
    linarith
  refine ⟨rawRadius, by dsimp only [rawRadius, angularRadius]; positivity,
    forcingRadius, by dsimp only [forcingRadius]; positivity,
    shapeRadius, by dsimp only [shapeRadius]; positivity, constant, constantOne, ?_⟩
  intro count family index first final firstInside finalInside firstMember finalMember firstPhysicalMember finalPhysicalMember
    firstArea finalArea firstCentered finalCentered frequency time distance weight radius nonzero positive weightNonnegative
    radiusNonnegative radiusSmall firstTransverse finalTransverse small separated weightBound forcingSmall epsilonSmall squaredSmall tailSmall
  have radiusOne : radius ≤ 1 := radiusSmall.trans (min_le_left _ _)
  have firstScale := ball_subset_ball (min_le_left _ _) firstInside
  have finalScale := ball_subset_ball (min_le_left _ _) finalInside
  have firstGeometry := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) firstInside
  have finalGeometry := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) finalInside
  have pair := geometry first final firstGeometry finalGeometry firstArea finalArea
  dsimp only at pair
  have within {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 rawRadius) :
      ‖diskNeutralCLM state‖ ≤ angularRadius ∧
      ‖diskRelabelCurve (diskNeutralCLM state) 1 - standardCircleBanach‖ < threshold := by
    have stateSmall : ‖state‖ ≤ rawRadius := (by simpa only [mem_ball, dist_zero_right] using inside : ‖state‖ < rawRadius).le
    have angularLe : rawRadius ≤ angularRadius / (1 + ‖diskNeutralCLM‖) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have scaled := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskNeutralCLM‖)).mp (stateSmall.trans angularLe)
    have angularBound : ‖diskNeutralCLM state‖ ≤ angularRadius := by
      nlinarith [diskNeutralCLM.le_opNorm state, norm_nonneg state]
    refine ⟨angularBound, bases ?_⟩
    simpa only [mem_ball, dist_zero_right] using
      (ball_subset_ball ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) inside : state ∈ ball 0 baseRadius)
  have firstWithin := within firstInside
  have finalWithin := within finalInside
  have firstHalf : ‖diskNeutralCLM first‖ < 1 / 2 := (firstWithin.1.trans (min_le_right _ _)).trans_lt (by norm_num)
  have finalHalf : ‖diskNeutralCLM final‖ < 1 / 2 := (finalWithin.1.trans (min_le_right _ _)).trans_lt (by norm_num)
  have firstAngularMember := diskNeutralCLM_mem_contourContinuousVectorSubmodule first firstMember
  have finalAngularMember := diskNeutralCLM_mem_contourContinuousVectorSubmodule final finalMember
  have firstBaseMember := diskRelabelCurve_mem_contourContinuousVectorSubmodule _ firstHalf (diskNeutralCLM_real first) firstAngularMember
  have finalBaseMember := diskRelabelCurve_mem_contourContinuousVectorSubmodule _ finalHalf (diskNeutralCLM_real final) finalAngularMember
  have baseCentroid (state : PeriodicC1HolderHalf) (half : ‖diskNeutralCLM state‖ < 1 / 2) :
      contourCentroidFunctional (diskRelabelCurve (diskNeutralCLM state) 1) = 0 := by
    rw [← fixedRelabelEquivalence_circle _ half (diskNeutralCLM_real state),
      contourCentroidFunctional_fixedRelabel, contourCentroidFunctional_standardCircle_zero]
  have firstCentroid : contourCentroidFunctional
      (diskRelabelCurve (diskNeutralCLM first) 1 + (diskPhysicalSpectralChart first - diskRelabelCurve (diskNeutralCLM first) 1)) =
        contourCentroidFunctional (diskRelabelCurve (diskNeutralCLM first) 1) := by
    simpa only [add_sub_cancel, firstCentered, baseCentroid first firstHalf]
  have finalCentroid : contourCentroidFunctional
      (diskRelabelCurve (diskNeutralCLM final) 1 + (diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1)) =
        contourCentroidFunctional (diskRelabelCurve (diskNeutralCLM final) 1) := by
    simpa only [add_sub_cancel, finalCentered, baseCentroid final finalHalf]
  have firstIncrement := pair.1.trans (mul_le_mul_of_nonneg_left firstTransverse geometryPositiveConstant.le)
  have finalIncrement := pair.2.1.trans (mul_le_mul_of_nonneg_left finalTransverse geometryPositiveConstant.le)
  have incrementCap : ‖diskPhysicalSpectralChart first - diskRelabelCurve (diskNeutralCLM first) 1‖ +
      ‖diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1‖ ≤ assemblyRadius / 4 := by
    have scaled := (le_div_iff₀ (by positivity : 0 < 8 * geometryConstant)).mp
      (radiusSmall.trans (min_le_right _ _))
    linarith
  have shiftCap {state : PeriodicC1HolderHalf} (inside : ‖diskNeutralCLM state‖ ≤ angularRadius)
      (increment : ‖diskPhysicalSpectralChart state - diskRelabelCurve (diskNeutralCLM state) 1‖ ≤ geometryConstant * radius) :
      ‖diskPhysicalSpectralChart state - family.canonicalExteriorAffineCoordinate index (diskNeutralCLM state)
        frequency time (diskPhysicalSpectralChart state)‖ ≤ assemblyRadius / 8 := by
    have actual := shifts family index (diskNeutralCLM state) (inside.trans (min_le_left _ _)) (diskNeutralCLM_real state)
      nonzero positive weightNonnegative (by linarith [(family.patch index).radius_positive]) separated weightBound (diskPhysicalSpectralChart state)
    rw [norm_sub_rev] at actual
    have incrementOne := increment.trans (mul_le_mul_of_nonneg_left radiusOne geometryPositiveConstant.le)
    have bounded := actual.trans (mul_le_mul_of_nonneg_left (add_le_add_left incrementOne 1) (by positivity))
    have scaled := (le_div_iff₀ (by positivity : 0 < 8 * shiftConstant * (1 + geometryConstant))).mp forcingSmall
    nlinarith only [bounded, scaled]
  have firstShift := shiftCap firstWithin.1 firstIncrement
  have finalShift := shiftCap finalWithin.1 finalIncrement
  have bound := assembly family family index index (diskNeutralCLM first) (diskNeutralCLM final) firstHalf finalHalf
    firstAngularMember finalAngularMember (diskNeutralCLM_real first) (diskNeutralCLM_real final)
    (firstWithin.2.trans_le (min_le_right _ _)) (finalWithin.2.trans_le (min_le_right _ _))
    (diskPhysicalSpectralChart first - diskRelabelCurve (diskNeutralCLM first) 1)
    (diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1)
    (contourContinuousVectorSubmodule.sub_mem firstPhysicalMember firstBaseMember)
    (contourContinuousVectorSubmodule.sub_mem finalPhysicalMember finalBaseMember)
    firstCentroid finalCentroid nonzero positive positive separated separated small small
  dsimp only at bound
  simp only [add_sub_cancel] at bound
  have firstJoint :
      ‖diskRelabelCurve (diskNeutralCLM first) 1 - standardCircleBanach‖ +
        (‖diskPhysicalSpectralChart first - diskRelabelCurve (diskNeutralCLM first) 1‖ +
          ‖diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1‖) +
        (‖diskPhysicalSpectralChart first - family.canonicalExteriorAffineCoordinate index (diskNeutralCLM first) frequency time (diskPhysicalSpectralChart first)‖ +
          ‖diskPhysicalSpectralChart final - family.canonicalExteriorAffineCoordinate index (diskNeutralCLM final) frequency time (diskPhysicalSpectralChart final)‖) ≤ assemblyRadius := by
    have baseCap := firstWithin.2.le.trans (min_le_left _ _)
    linarith
  have finalJoint :
      ‖diskRelabelCurve (diskNeutralCLM final) 1 - standardCircleBanach‖ +
        (‖diskPhysicalSpectralChart first - diskRelabelCurve (diskNeutralCLM first) 1‖ +
          ‖diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1‖) +
        (‖diskPhysicalSpectralChart first - family.canonicalExteriorAffineCoordinate index (diskNeutralCLM first) frequency time (diskPhysicalSpectralChart first)‖ +
          ‖diskPhysicalSpectralChart final - family.canonicalExteriorAffineCoordinate index (diskNeutralCLM final) frequency time (diskPhysicalSpectralChart final)‖) ≤ assemblyRadius := by
    have baseCap := finalWithin.2.le.trans (min_le_left _ _)
    linarith
  have residual := bound firstJoint finalJoint
  have scale := scales family index first final firstScale finalScale firstArea finalArea nonzero positive weightNonnegative
    radiusNonnegative radiusOne firstTransverse finalTransverse small separated weightBound
  dsimp only at scale
  have quadratic := EulerNonuniqueness.General.exteriorStaticResidualScaleModel_le_quadratic_rate
    (transverse := ‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖)
    (angular := ‖diskNeutralCLM first - diskNeutralCLM final‖)
    (abs_pos.mpr nonzero) scaleNonnegative (by positivity : 0 ≤ weight / |frequency|) radiusNonnegative radiusOne
    (div_nonneg (family.patch index).radius_positive.le positive.le) (norm_nonneg _) (norm_nonneg _)
    epsilonSmall squaredSmall tailSmall
  have actual := residual.trans (mul_le_mul_of_nonneg_left (scale.trans quadratic) assemblyNonnegative)
  have coefficientLe : assemblyConstant * 3 * polynomial ≤ constant := by dsimp only [constant]; linarith
  have scalar := mul_le_mul_of_nonneg_right coefficientLe (by positivity : 0 ≤ |frequency| * radius ^ 2 *
    (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ + radius * ‖diskNeutralCLM first - diskNeutralCLM final‖))
  with_reducible_and_instances
    calc
      _ ≤ assemblyConstant * (3 * |frequency| * polynomial * radius ^ 2 *
          (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
            radius * ‖diskNeutralCLM first - diskNeutralCLM final‖)) := actual
      _ = (assemblyConstant * 3 * polynomial) * (|frequency| * radius ^ 2 *
          (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
            radius * ‖diskNeutralCLM first - diskNeutralCLM final‖)) := by ring
      _ ≤ constant * (|frequency| * radius ^ 2 *
          (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
            radius * ‖diskNeutralCLM first - diskNeutralCLM final‖)) := scalar
      _ = _ := by ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
