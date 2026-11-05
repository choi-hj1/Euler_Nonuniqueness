import EulerNonuniqueness.Section3.CanonicalExteriorFirstAmplitudeMaterialRelative
import EulerNonuniqueness.Section3.DiskTrueAngularPhysicalPairBounds

noncomputable section

open Filter Metric MeasureTheory Set
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorFirstAmplitudeError_exists_actual_quadratic_rate_ball :
    ∃ rawRadius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (first final : PeriodicC1HolderHalf), first ∈ ball 0 rawRadius → final ∈ ball 0 rawRadius →
      diskSpectralTubularArea first = Real.pi → diskSpectralTubularArea final = Real.pi →
      ∀ (firstSmall : ‖diskNeutralCLM first‖ < 1 / 2) (finalSmall : ‖diskNeutralCLM final‖ < 1 / 2),
      ∀ {frequency time distance weight mass radius : ℝ}, frequency ≠ 0 →
      time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime →
      (∀ label, (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label)) →
      (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid →
      0 < distance → 0 ≤ weight → 0 ≤ mass → 0 ≤ radius → radius ≤ 1 →
      ‖diskPhysicalTransverseProjection first‖ ≤ radius → ‖diskPhysicalTransverseProjection final‖ ≤ radius →
      192 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      (∫ position, |family.patchVorticity time index position|) ≤ mass →
      (12 * (46 * weight ^ 2 / Real.pi ^ 2 + 6 * mass * weight / (Real.pi ^ 2 * distance ^ 2))) / |frequency| ≤
        |frequency| * radius ^ 3 →
      ‖(fixedRelabelEquivalence (diskNeutralCLM first) firstSmall
          (family.exteriorAmplitudeDerivativePrimitive index frequency time) +
        family.exteriorStrainAmplitudeCorrection index (diskNeutralCLM first) frequency time
          (diskPhysicalSpectralChart first - diskRelabelCurve (diskNeutralCLM first) 1)) -
        (fixedRelabelEquivalence (diskNeutralCLM final) finalSmall
          (family.exteriorAmplitudeDerivativePrimitive index frequency time) +
        family.exteriorStrainAmplitudeCorrection index (diskNeutralCLM final) frequency time
          (diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1))‖ ≤
        constant * |frequency| * radius ^ 2 *
          (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
            radius * ‖diskNeutralCLM first - diskNeutralCLM final‖) := by
  obtain ⟨amplitudeRadius, amplitudePositive, amplitudeConstant, amplitudeOne, amplitudes⟩ :=
    canonicalExteriorFirstAmplitudeError_exists_material_relative_ball
  obtain ⟨geometryRadius, geometryPositive, geometryConstant, geometryOne, geometry⟩ :=
    diskPhysicalSpectralChart_exists_true_angular_pair_bounds
  have geometryNonnegative : 0 ≤ geometryConstant := by linarith
  have amplitudeNonnegative : 0 ≤ amplitudeConstant := by linarith
  have baseSmall : ∀ᶠ angular in 𝓝 (0 : PeriodicC1HolderHalf), ‖diskRelabelCurve angular 1‖ < 3 := by
    have circle : diskRelabelCurve (0 : PeriodicC1HolderHalf) 1 = standardCircleBanach := by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      rw [diskRelabelCurve_value]
      change Complex.exp ((1 : ℂ) * (Complex.I * 0)) * standardCircle label = standardCircle label
      simp
    exact (diskRelabelMap_analyticAt 0).continuousAt.norm.eventually (gt_mem_nhds (by
      change ‖diskRelabelCurve (0 : PeriodicC1HolderHalf) 1‖ < 3
      rw [circle]
      linarith [standardCircleBanach_norm_bound]))
  obtain ⟨baseRadius, basePositive, bases⟩ := Metric.eventually_nhds_iff.mp baseSmall
  let angularRadius := min amplitudeRadius (baseRadius / 2)
  let rawRadius := min geometryRadius (angularRadius / (1 + ‖diskNeutralCLM‖))
  let constant := amplitudeConstant * (2 * geometryConstant + 1) + 1
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ amplitudeConstant * (2 * geometryConstant + 1) := by positivity
    dsimp only [constant]
    linarith
  refine ⟨rawRadius, by dsimp only [rawRadius, angularRadius]; positivity, constant, constantOne, ?_⟩
  intro count family index first final firstInside finalInside firstArea finalArea firstSmall finalSmall frequency time distance
    weight mass radius nonzero timeInside material centered positive weightNonnegative massNonnegative radiusNonnegative radiusSmall
    firstTransverse finalTransverse small separated weightBound massBound derivativeScale
  have within {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 rawRadius) :
      ‖diskNeutralCLM state‖ ≤ amplitudeRadius ∧ ‖diskRelabelCurve (diskNeutralCLM state) 1‖ ≤ 3 := by
    have stateSmall : ‖state‖ ≤ rawRadius := (by simpa only [mem_ball, dist_zero_right] using inside : ‖state‖ < rawRadius).le
    have scaled := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskNeutralCLM‖)).mp (stateSmall.trans (min_le_right _ _))
    have angular : ‖diskNeutralCLM state‖ ≤ angularRadius := by nlinarith [diskNeutralCLM.le_opNorm state, norm_nonneg state]
    refine ⟨angular.trans (min_le_left _ _), (bases ?_).le⟩
    rw [dist_zero_right]
    exact (angular.trans (min_le_right _ _)).trans_lt (half_lt_self basePositive)
  have firstWithin := within firstInside
  have finalWithin := within finalInside
  have pair := geometry first final (ball_subset_ball (min_le_left _ _) firstInside)
    (ball_subset_ball (min_le_left _ _) finalInside) firstArea finalArea
  dsimp only at pair
  let transverse := ‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖
  let angular := ‖diskNeutralCLM first - diskNeutralCLM final‖
  have transverseNonnegative : 0 ≤ transverse := norm_nonneg _
  have angularNonnegative : 0 ≤ angular := norm_nonneg _
  have incrementCap := (pair.2.1.trans (mul_le_mul_of_nonneg_left finalTransverse geometryNonnegative)).trans
    (mul_le_mul_of_nonneg_left radiusSmall geometryNonnegative)
  have geometric : ‖diskPhysicalSpectralChart first - diskPhysicalSpectralChart final‖ +
      (1 + ‖diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1‖) * angular ≤
      (2 * geometryConstant + 1) * (transverse + angular) := by
    have bounded := add_le_add pair.2.2.2.2 (mul_le_mul_of_nonneg_right (add_le_add_left incrementCap 1) angularNonnegative)
    have leftover : 0 ≤ (geometryConstant + 1) * transverse := by positivity
    nlinarith only [bounded, leftover]
  have actual := amplitudes family index (diskNeutralCLM first) (diskNeutralCLM final) firstSmall finalSmall
    firstWithin.1 finalWithin.1 (diskNeutralCLM_real first) (diskNeutralCLM_real final) firstWithin.2 finalWithin.2
    nonzero timeInside material centered positive weightNonnegative massNonnegative small separated weightBound massBound
    (diskPhysicalSpectralChart first) (diskPhysicalSpectralChart final)
  have bounded := actual.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left derivativeScale amplitudeNonnegative) geometric (by positivity) (by positivity))
  have cubeLeSquare : radius ^ 3 ≤ radius ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg radius) (sub_nonneg.mpr radiusSmall)]
  have weighted : radius ^ 3 * (transverse + angular) ≤ radius ^ 2 * (transverse + radius * angular) := by
    nlinarith [mul_le_mul_of_nonneg_right cubeLeSquare transverseNonnegative]
  have scaled := mul_le_mul_of_nonneg_left weighted
    (by positivity : 0 ≤ amplitudeConstant * (2 * geometryConstant + 1) * |frequency|)
  have coefficientLe : amplitudeConstant * (2 * geometryConstant + 1) ≤ constant := by dsimp only [constant]; linarith
  have scalar := mul_le_mul_of_nonneg_right coefficientLe (by positivity : 0 ≤ |frequency| * radius ^ 2 * (transverse + radius * angular))
  exact ((bounded.trans_eq (by ring)).trans scaled).trans (by convert scalar using 1 <;> ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
