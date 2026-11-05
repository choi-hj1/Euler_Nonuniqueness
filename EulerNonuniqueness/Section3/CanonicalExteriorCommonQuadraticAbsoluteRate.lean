import EulerNonuniqueness.Section3.CanonicalExteriorCommonMaterialAbsolute
import EulerNonuniqueness.Section3.CanonicalExteriorCommonQuadraticHistory
import EulerNonuniqueness.Section3.DiskNormalizedQuadraticErrorRelative
import EulerNonuniqueness.Section3.DiskQuadraticSelfAbsoluteRate

noncomputable section

open Filter Metric MeasureTheory Set
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

local instance commonQuadraticAbsoluteRateC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

open EulerNonuniqueness.Section6

theorem canonicalExteriorCommonQuadraticMaterialForcing_exists_actual_cubic_bound_ball :
    ∃ rawRadius > 0, ∃ physicalRadius > 0, ∃ spectralRadius > 0, ∃ forcingRadius > 0, ∃ constant ≥ 1,
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
      ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state) - standardCircleBanach‖ ≤ physicalRadius →
      ‖family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state)‖ ≤ spectralRadius →
      diskSpectralTubularArea (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state)) = Real.pi →
      ‖diskPhysicalTransverseProjection (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state))‖ ≤ radius →
      ‖family.canonicalExteriorCommonQuadraticMaterialForcing index frequency time (diskPhysicalSpectralChart state)
        (family.canonicalExteriorCommonMaterialResidual index frequency time distance positive
          (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart state) angularSmall) 0‖ ≤
        constant * |frequency| * radius ^ 3 := by
  obtain ⟨rawRadius, rawPositive, forcingRadius, forcingPositive, materialConstant, materialOne, materials⟩ :=
    canonicalExteriorCommonMaterialResidual_exists_actual_cubic_bound_ball
  obtain ⟨physicalRadius, physicalPositive, errorConstant, errorOne, errors, _⟩ :=
    diskNormalizedQuadraticError_exists_uniform_pair_ball
  obtain ⟨selfRadius, selfPositive, selfConstant, selfOne, selfs⟩ :=
    diskSpectralMovingSelfRemainder_exists_absolute_cubic_ball
  let constant := selfConstant + errorConstant * materialConstant + 1
  have selfNonnegative : 0 ≤ selfConstant := by linarith
  have errorNonnegative : 0 ≤ errorConstant := by linarith
  have materialNonnegative : 0 ≤ materialConstant := by linarith
  have constantOne : 1 ≤ constant := by
    have productNonnegative := mul_nonneg errorNonnegative materialNonnegative
    dsimp only [constant]
    linarith
  refine ⟨rawRadius, rawPositive, physicalRadius, physicalPositive, selfRadius / 2, by positivity,
    forcingRadius, forcingPositive, constant, constantOne, ?_⟩
  intro count family index state inside member physicalMember area centered angularSmall frequency time distance weight mass radius
    nonzero timeInside material centerIdentity positive weightNonnegative massNonnegative radiusNonnegative radiusSmall transverseSmall
    small separated weightBound massBound forcingSmall epsilonSmall squaredSmall tailSmall derivativeScale
    physicalInside spectralInside correctedArea correctedTransverse
  have materialBound := materials family index state inside member physicalMember area centered angularSmall nonzero timeInside
    material centerIdentity positive weightNonnegative massNonnegative radiusNonnegative radiusSmall transverseSmall small separated
    weightBound massBound forcingSmall epsilonSmall squaredSmall tailSmall derivativeScale
  let corrected := family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state)
  let residual := family.canonicalExteriorCommonMaterialResidual index frequency time distance positive
    (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart state) angularSmall
  have correctedInside : corrected ∈ ball 0 selfRadius := by
    with_reducible_and_instances
      simpa only [mem_ball, dist_zero_right, corrected] using spectralInside.trans_lt (half_lt_self selfPositive)
  have selfBound := selfs corrected correctedInside correctedArea
  have cubedCap := pow_le_pow_left₀ (norm_nonneg (diskPhysicalTransverseProjection corrected)) correctedTransverse 3
  have selfScaled : ‖frequency • diskSpectralMovingSelfRemainder corrected‖ ≤ selfConstant * |frequency| * radius ^ 3 := by
    with_reducible_and_instances
      rw [norm_smul, Real.norm_eq_abs]
      exact ((mul_le_mul_of_nonneg_left selfBound (abs_nonneg frequency)).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left cubedCap selfNonnegative) (abs_nonneg frequency))).trans_eq (by ring)
  have errorBound := errors
    (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state)) residual physicalInside
  have errorScaled : ‖diskNormalizedQuadraticError
      (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state)) residual‖ ≤
      (errorConstant * materialConstant) * |frequency| * radius ^ 3 := by
    with_reducible_and_instances
      exact (errorBound.trans (mul_le_mul_of_nonneg_left materialBound errorNonnegative)).trans_eq (by ring)
  have sumBound := (norm_add_le (frequency • diskSpectralMovingSelfRemainder corrected)
    (diskNormalizedQuadraticError
      (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state)) residual)).trans
        (add_le_add selfScaled errorScaled)
  have coefficientLe : selfConstant + errorConstant * materialConstant ≤ constant := by dsimp only [constant]; linarith
  have scalar := mul_le_mul_of_nonneg_right coefficientLe (by positivity : 0 ≤ |frequency| * radius ^ 3)
  have result : ‖frequency • diskSpectralMovingSelfRemainder corrected +
      diskNormalizedQuadraticError
        (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state)) residual‖ ≤
      constant * |frequency| * radius ^ 3 := by
    exact sumBound.trans ((by ring : selfConstant * |frequency| * radius ^ 3 +
      (errorConstant * materialConstant) * |frequency| * radius ^ 3 =
        (selfConstant + errorConstant * materialConstant) * (|frequency| * radius ^ 3)).le.trans (scalar.trans_eq (by ring)))
  with_reducible_and_instances
    simpa only [canonicalExteriorCommonQuadraticMaterialForcing, diskNormalizedQuadraticError,
      canonicalExteriorCommonNormalizedPhysicalCoordinate, corrected, residual, map_zero, add_zero] using result

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
