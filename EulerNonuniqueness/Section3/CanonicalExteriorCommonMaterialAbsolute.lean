import EulerNonuniqueness.Section3.CanonicalExteriorCommonMaterialField
import EulerNonuniqueness.Section3.CanonicalExteriorMovingAngularAbsolute
import EulerNonuniqueness.Section3.CanonicalExteriorAffineMaterialErrorBound
import EulerNonuniqueness.Section3.MovingStrainSpectralRelabelDomain
import EulerNonuniqueness.Section3.RelabeledPrimitiveContinuousVectors
import EulerNonuniqueness.Section3.DiskNeutralContinuousVectors
import EulerNonuniqueness.General.ExteriorAmplitudeDerivativeScale

noncomputable section

open Filter Metric MeasureTheory Set
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorCommonMaterialResidual_exists_actual_cubic_bound_ball :
    ∃ rawRadius > 0, ∃ forcingRadius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (state : PeriodicC1HolderHalf), state ∈ ball 0 rawRadius →
      state ∈ contourContinuousVectorSubmodule → diskPhysicalSpectralChart state ∈ contourContinuousVectorSubmodule →
      diskSpectralTubularArea state = Real.pi → contourCentroidFunctional (diskPhysicalSpectralChart state) = 0 →
      ∀ (angularSmall : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart state))‖ < 1 / 2),
      ∀ {frequency time distance weight mass radius : ℝ}, frequency ≠ 0 →
      time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime →
      (∀ label, (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label)) →
      (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid →
      ∀ (positive : 0 < distance) (weightNonnegative : 0 ≤ weight),
      0 ≤ mass → 0 ≤ radius → radius ≤ 1 → ‖diskPhysicalTransverseProjection state‖ ≤ radius →
      ∀ (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖),
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      (∫ position, |family.patchVorticity time index position|) ≤ mass →
      weight / |frequency| ≤ forcingRadius → weight / |frequency| ≤ radius →
      (weight / |frequency|) ^ 2 ≤ radius ^ 3 →
      (weight / |frequency|) * ((family.patch index).radius / distance) ≤ radius ^ 2 →
      (12 * (46 * weight ^ 2 / Real.pi ^ 2 + 6 * mass * weight / (Real.pi ^ 2 * distance ^ 2))) / |frequency| ≤
        |frequency| * radius ^ 3 →
      ‖family.canonicalExteriorCommonMaterialResidual index frequency time distance positive
          (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart state) angularSmall‖ ≤
        constant * |frequency| * radius ^ 3 := by
  obtain ⟨materialRadius, materialPositive, materialConstant, materialOne, materials⟩ :=
    canonicalExteriorAffineMaterialError_exists_uniform_bound
  obtain ⟨angularRadius, angularPositive, angularConstant, angularOne, angulars⟩ :=
    canonicalExteriorCommonMovingAngularTerm_exists_actual_cubic_bound_ball
  obtain ⟨geometryRadius, geometryPositive, geometryConstant, geometryOne, geometry⟩ :=
    diskPhysicalSpectralChart_exists_true_angular_pair_bounds
  obtain ⟨domainRadius, domainPositive, domains⟩ := movingStrainSpectral_exists_relabel_domain
    (show 0 < materialRadius / 2 by positivity)
  obtain ⟨inverseRadius, inversePositive, inverses⟩ := Metric.eventually_nhds_iff.mp
    diskPhysicalSpectralCoordinate_eventually_left_inverse
  let rawRadius := min angularRadius (min geometryRadius (min domainRadius
    (min inverseRadius (materialRadius / (1 + ‖diskNeutralCLM‖)))))
  let constant := materialConstant * (geometryConstant ^ 2 + geometryConstant + Real.pi ^ 2 / 72) + angularConstant + 1
  have materialNonnegative : 0 ≤ materialConstant := by linarith
  have geometryNonnegative : 0 ≤ geometryConstant := by linarith
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ materialConstant * (geometryConstant ^ 2 + geometryConstant + Real.pi ^ 2 / 72) := by positivity
    dsimp only [constant]
    linarith
  refine ⟨rawRadius, by dsimp only [rawRadius]; positivity, materialRadius, materialPositive, constant, constantOne, ?_⟩
  intro count family index state inside member physicalMember area centered angularSmall frequency time distance weight mass radius
    nonzero timeInside material centerIdentity positive weightNonnegative massNonnegative radiusNonnegative radiusSmall transverseSmall
    small separated weightBound massBound forcingSmall epsilonSmall squaredSmall tailSmall derivativeScale
  have restrict {outer : ℝ} (ordered : rawRadius ≤ outer) : state ∈ ball 0 outer := ball_subset_ball ordered inside
  have domain := domains state (restrict ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have stateInverse : diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart state) = state := by
    apply inverses
    simpa only [mem_ball, dist_zero_right] using
      restrict ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have baseIdentity := movingStrainSpectral_stationary_base_eq_fixedRelabel state domain.1
  rw [fixedRelabelEquivalence_circle _ domain.1 (diskNeutralCLM_real state)] at baseIdentity
  have angularNear : ‖diskNeutralCLM state‖ ≤ materialRadius := by
    have stateSmall : ‖state‖ ≤ rawRadius := (by simpa only [mem_ball, dist_zero_right] using inside : ‖state‖ < rawRadius).le
    have scaled := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskNeutralCLM‖)).mp
      (stateSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
    nlinarith [diskNeutralCLM.le_opNorm state, norm_nonneg state]
  let increment := diskPhysicalSpectralChart state - diskRelabelCurve (diskNeutralCLM state) 1
  have incrementIdentity : increment = diskPhysicalSpectralDefect state := by
    simp only [increment, diskPhysicalSpectralDefect, baseIdentity]
  have angularMember := diskNeutralCLM_mem_contourContinuousVectorSubmodule state member
  have baseMember := diskRelabelCurve_mem_contourContinuousVectorSubmodule _ domain.1 (diskNeutralCLM_real state) angularMember
  have incrementMember : increment ∈ contourContinuousVectorSubmodule := contourContinuousVectorSubmodule.sub_mem physicalMember baseMember
  have joint : ‖diskRelabelCurve (diskNeutralCLM state) 1 - standardCircleBanach‖ + ‖increment‖ ≤ materialRadius := by
    rw [incrementIdentity, ← baseIdentity]
    linarith [domain.2.2.1, domain.2.2.2]
  have centroidIdentity : contourCentroidFunctional (diskRelabelCurve (diskNeutralCLM state) 1 + increment) =
      contourCentroidFunctional (diskRelabelCurve (diskNeutralCLM state) 1) := by
    simp only [increment, add_sub_cancel, centered]
    rw [← fixedRelabelEquivalence_circle _ domain.1 (diskNeutralCLM_real state),
      contourCentroidFunctional_fixedRelabel, contourCentroidFunctional_standardCircle_zero]
  have materialBound := materials family index (diskNeutralCLM state) increment domain.1 angularNear angularMember incrementMember
    (diskNeutralCLM_real state) nonzero timeInside material centerIdentity positive weightNonnegative massNonnegative small separated
    weightBound massBound joint forcingSmall centroidIdentity
  have pair := geometry state state
    (restrict ((min_le_right _ _).trans (min_le_left _ _)))
    (restrict ((min_le_right _ _).trans (min_le_left _ _))) area area
  dsimp only at pair
  have incrementCap : ‖increment‖ ≤ geometryConstant * radius :=
    pair.1.trans (mul_le_mul_of_nonneg_left transverseSmall geometryNonnegative)
  have valueBound := (EulerNonuniqueness.General.exteriorAmplitudeValueScale_le_derivativeScale
    (abs_pos.mpr nonzero) positive weightNonnegative massNonnegative).trans
      (mul_le_mul_of_nonneg_left derivativeScale (by positivity : 0 ≤ Real.pi ^ 2 / 72))
  have scalar := EulerNonuniqueness.General.exteriorAffineMaterialScale_le_cubic_rate
    (frequencyPositive := abs_pos.mpr nonzero) materialNonnegative geometryNonnegative
    (by positivity : 0 ≤ weight / |frequency|) radiusNonnegative
    (div_nonneg (family.patch index).radius_positive.le positive.le) (norm_nonneg increment) incrementCap
    epsilonSmall tailSmall (by convert valueBound using 1 <;> ring)
  have normalization : |frequency| * (weight / |frequency|) = weight := mul_div_cancel₀ weight (abs_pos.mpr nonzero).ne'
  rw [normalization] at scalar
  have materialResult := materialBound.trans scalar
  have angularResult := angulars family index state (restrict (min_le_left _ _)) area nonzero positive weightNonnegative
    radiusNonnegative radiusSmall transverseSmall small separated weightBound epsilonSmall squaredSmall
  have identity : family.canonicalExteriorCommonMaterialResidual index frequency time distance positive
      (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart state) angularSmall =
      (family.canonicalExteriorAffinePhaseField index (diskNeutralCLM state) frequency time distance positive
        (by linarith [(family.patch index).radius_positive]) separated (diskRelabelCurve (diskNeutralCLM state) 1 + increment) -
      fixedRelabelEquivalence (diskNeutralCLM state) domain.1 (family.exteriorAmplitudeDerivativePrimitive index frequency time) -
      family.exteriorStrainAmplitudeCorrection index (diskNeutralCLM state) frequency time increment -
      frequency • diskEulerRotatingField
        (family.canonicalExteriorAffineCoordinate index (diskNeutralCLM state) frequency time
          (diskRelabelCurve (diskNeutralCLM state) 1 + increment))) +
      family.canonicalExteriorCommonMovingAngularTerm index frequency time distance positive
        (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart state) := by
    simp only [canonicalExteriorCommonMaterialResidual, canonicalExteriorStaticPhaseResidual,
      canonicalExteriorCommonMovingAngularTerm, stateInverse, increment, add_sub_cancel]
    abel
  rw [identity]
  have bounded := (norm_add_le _ _).trans (add_le_add materialResult angularResult)
  have coefficientLe : materialConstant * (geometryConstant ^ 2 + geometryConstant + Real.pi ^ 2 / 72) + angularConstant ≤ constant := by
    dsimp only [constant]
    linarith
  have scaled := mul_le_mul_of_nonneg_right coefficientLe (by positivity : 0 ≤ |frequency| * radius ^ 3)
  exact (bounded.trans_eq (by ring)).trans (scaled.trans_eq (by ring))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
