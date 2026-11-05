import EulerNonuniqueness.Section3.CanonicalExteriorActualStaticRate
import EulerNonuniqueness.Section3.CanonicalExteriorMovingAngularRate
import EulerNonuniqueness.Section3.CanonicalExteriorFirstAmplitudeStateRate
import EulerNonuniqueness.Section3.CanonicalExteriorCommonMaterialField

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

theorem canonicalExteriorCommonMaterialResidual_exists_actual_quadratic_rate_ball :
    ∃ rawRadius > 0, ∃ forcingRadius > 0, ∃ shapeRadius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (first final : PeriodicC1HolderHalf), first ∈ ball 0 rawRadius → final ∈ ball 0 rawRadius →
      first ∈ contourContinuousVectorSubmodule → final ∈ contourContinuousVectorSubmodule →
      diskPhysicalSpectralChart first ∈ contourContinuousVectorSubmodule →
      diskPhysicalSpectralChart final ∈ contourContinuousVectorSubmodule →
      diskSpectralTubularArea first = Real.pi → diskSpectralTubularArea final = Real.pi →
      contourCentroidFunctional (diskPhysicalSpectralChart first) = 0 →
      contourCentroidFunctional (diskPhysicalSpectralChart final) = 0 →
      ∀ (firstSmall : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart first))‖ < 1 / 2)
        (finalSmall : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart final))‖ < 1 / 2),
      ∀ {frequency time distance weight mass radius : ℝ}, frequency ≠ 0 →
      time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime →
      (∀ label, (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label)) →
      (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid →
      ∀ (positive : 0 < distance) (weightNonnegative : 0 ≤ weight),
      0 ≤ mass → 0 ≤ radius → radius ≤ shapeRadius →
      ‖diskPhysicalTransverseProjection first‖ ≤ radius → ‖diskPhysicalTransverseProjection final‖ ≤ radius →
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
          (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart first) firstSmall -
        family.canonicalExteriorCommonMaterialResidual index frequency time distance positive
          (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart final) finalSmall‖ ≤
        constant * |frequency| * radius ^ 2 *
          (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
            radius * ‖diskNeutralCLM first - diskNeutralCLM final‖) := by
  obtain ⟨staticRadius, staticPositive, forcingRadius, forcingPositive, shapeRadius, shapePositive,
    staticConstant, staticOne, statics⟩ := canonicalExteriorStaticPhaseResidual_exists_actual_quadratic_rate_ball
  obtain ⟨angularRadius, angularPositive, angularConstant, angularOne, angulars⟩ :=
    canonicalExteriorCommonMovingAngularTerm_exists_actual_quadratic_rate_ball
  obtain ⟨amplitudeRadius, amplitudePositive, amplitudeConstant, amplitudeOne, amplitudes⟩ :=
    canonicalExteriorFirstAmplitudeError_exists_actual_quadratic_rate_ball
  obtain ⟨inverseRadius, inversePositive, inverses⟩ := Metric.eventually_nhds_iff.mp
    diskPhysicalSpectralCoordinate_eventually_left_inverse
  let rawRadius := min staticRadius (min angularRadius (min amplitudeRadius inverseRadius))
  let constant := staticConstant + angularConstant + amplitudeConstant + 1
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith
  refine ⟨rawRadius, by dsimp only [rawRadius]; positivity, forcingRadius, forcingPositive,
    min shapeRadius 1, lt_min shapePositive (by norm_num), constant, constantOne, ?_⟩
  intro count family index first final firstInside finalInside firstMember finalMember firstPhysicalMember finalPhysicalMember
    firstArea finalArea firstCentered finalCentered firstSmall finalSmall frequency time distance weight mass radius
    nonzero timeInside material centered positive weightNonnegative massNonnegative radiusNonnegative radiusSmall
    firstTransverse finalTransverse small separated weightBound massBound forcingSmall epsilonSmall squaredSmall tailSmall derivativeScale
  have restrict {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 rawRadius) {outer : ℝ}
      (ordered : rawRadius ≤ outer) : state ∈ ball 0 outer := ball_subset_ball ordered inside
  have inverse {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 rawRadius) :
      diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart state) = state := by
    apply inverses
    simpa only [mem_ball, dist_zero_right] using
      restrict inside ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have firstInverse := inverse firstInside
  have finalInverse := inverse finalInside
  have firstHalf : ‖diskNeutralCLM first‖ < 1 / 2 := by simpa only [firstInverse] using firstSmall
  have finalHalf : ‖diskNeutralCLM final‖ < 1 / 2 := by simpa only [finalInverse] using finalSmall
  have radiusOne := radiusSmall.trans (min_le_right _ _)
  have static := statics family index first final (restrict firstInside (min_le_left _ _)) (restrict finalInside (min_le_left _ _))
    firstMember finalMember firstPhysicalMember finalPhysicalMember firstArea finalArea firstCentered finalCentered
    nonzero positive weightNonnegative radiusNonnegative (radiusSmall.trans (min_le_left _ _))
    firstTransverse finalTransverse small separated weightBound forcingSmall epsilonSmall squaredSmall tailSmall
  have angular := angulars family index first final
    (restrict firstInside ((min_le_right _ _).trans (min_le_left _ _)))
    (restrict finalInside ((min_le_right _ _).trans (min_le_left _ _)))
    firstArea finalArea nonzero positive weightNonnegative radiusNonnegative radiusOne firstTransverse finalTransverse
    small separated weightBound epsilonSmall squaredSmall
  have amplitude := amplitudes family index first final
    (restrict firstInside ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    (restrict finalInside ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    firstArea finalArea firstHalf finalHalf nonzero timeInside material centered positive weightNonnegative massNonnegative
    radiusNonnegative radiusOne firstTransverse finalTransverse small separated weightBound massBound derivativeScale
  have split (firstStatic finalStatic firstAmplitude finalAmplitude firstMoving finalMoving : PeriodicC1HolderHalf) :
      ‖(firstStatic - firstAmplitude + firstMoving) - (finalStatic - finalAmplitude + finalMoving)‖ ≤
        ‖firstStatic - finalStatic‖ + ‖firstAmplitude - finalAmplitude‖ + ‖firstMoving - finalMoving‖ := by
    have identity : (firstStatic - firstAmplitude + firstMoving) - (finalStatic - finalAmplitude + finalMoving) =
        (firstStatic - finalStatic) - (firstAmplitude - finalAmplitude) + (firstMoving - finalMoving) := by abel
    rw [identity]
    exact (norm_add_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
  let firstAmplitude := fixedRelabelEquivalence (diskNeutralCLM first) firstHalf
      (family.exteriorAmplitudeDerivativePrimitive index frequency time) +
    family.exteriorStrainAmplitudeCorrection index (diskNeutralCLM first) frequency time
      (diskPhysicalSpectralChart first - diskRelabelCurve (diskNeutralCLM first) 1)
  let finalAmplitude := fixedRelabelEquivalence (diskNeutralCLM final) finalHalf
      (family.exteriorAmplitudeDerivativePrimitive index frequency time) +
    family.exteriorStrainAmplitudeCorrection index (diskNeutralCLM final) frequency time
      (diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1)
  have actual := split
    (family.canonicalExteriorStaticPhaseResidual index (diskNeutralCLM first) frequency time distance positive
      (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart first))
    (family.canonicalExteriorStaticPhaseResidual index (diskNeutralCLM final) frequency time distance positive
      (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart final))
    firstAmplitude finalAmplitude
    (family.canonicalExteriorCommonMovingAngularTerm index frequency time distance positive
      (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart first))
    (family.canonicalExteriorCommonMovingAngularTerm index frequency time distance positive
      (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart final))
  have bounded := actual.trans (add_le_add (add_le_add static amplitude) angular)
  have coefficientLe : staticConstant + amplitudeConstant + angularConstant ≤ constant := by dsimp only [constant]; linarith
  have scalar := mul_le_mul_of_nonneg_right coefficientLe (by positivity : 0 ≤ |frequency| * radius ^ 2 *
    (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ + radius * ‖diskNeutralCLM first - diskNeutralCLM final‖))
  have result := (bounded.trans_eq (by ring)).trans scalar
  have residualIdentity (state : PeriodicC1HolderHalf)
      (smallAngular : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart state))‖ < 1 / 2)
      (stateInverse : diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart state) = state)
      (stateHalf : ‖diskNeutralCLM state‖ < 1 / 2) :
      family.canonicalExteriorCommonMaterialResidual index frequency time distance positive
          (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart state) smallAngular =
        family.canonicalExteriorStaticPhaseResidual index (diskNeutralCLM state) frequency time distance positive
          (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart state) -
        (fixedRelabelEquivalence (diskNeutralCLM state) stateHalf (family.exteriorAmplitudeDerivativePrimitive index frequency time) +
          family.exteriorStrainAmplitudeCorrection index (diskNeutralCLM state) frequency time
            (diskPhysicalSpectralChart state - diskRelabelCurve (diskNeutralCLM state) 1)) +
        family.canonicalExteriorCommonMovingAngularTerm index frequency time distance positive
          (by linarith [(family.patch index).radius_positive]) separated (diskPhysicalSpectralChart state) := by
    simp only [canonicalExteriorCommonMaterialResidual, canonicalExteriorCommonMovingAngularTerm, stateInverse]
    abel
  rw [residualIdentity first firstSmall firstInverse firstHalf, residualIdentity final finalSmall finalInverse finalHalf]
  exact result.trans_eq (by ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
