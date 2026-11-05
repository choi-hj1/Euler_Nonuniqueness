import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundaryComparison
import EulerNonuniqueness.Section3.CanonicalExteriorCommonCoordinateCompatibility
import EulerNonuniqueness.Section3.CanonicalExteriorCommonRawAbsoluteShift
import EulerNonuniqueness.Section3.CanonicalExteriorAffineShift

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

local instance commonBoundaryShapeCapsC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

open EulerNonuniqueness.Section6

theorem canonicalExteriorCommonRawSpectralCoordinate_exists_boundary_shape_caps
    (caps : CanonicalCommonBoundaryRateCaps) :
    ∃ rawRadius > 0, ∃ forcingRadius > 0, forcingRadius ≤ caps.forcingRadius ∧ ∃ shiftConstant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (state : PeriodicC1HolderHalf), state ∈ ball 0 rawRadius →
      diskSpectralTubularArea state = Real.pi → contourCentroidFunctional (diskPhysicalSpectralChart state) = 0 →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      192 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      weight / |frequency| ≤ forcingRadius →
      state ∈ ball 0 caps.rawRadius ∧
      ‖diskNeutralCLM (diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart state))‖ < 1 / 2 ∧
      ‖diskPhysicalSpectralChart state - standardCircleBanach‖ ≤ caps.fieldRadius ∧
      ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state) - standardCircleBanach‖ ≤ caps.physicalRadius ∧
      ‖family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state)‖ ≤ caps.spectralRadius ∧
      diskSpectralTubularArea
        (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state)) = Real.pi ∧
      ‖diskPhysicalTransverseProjection
        (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state))‖ ≤
        ‖diskPhysicalTransverseProjection state‖ + ‖diskPhysicalTransverseProjection‖ * (shiftConstant * (weight / |frequency|)) := by
  obtain ⟨shiftRaw, shiftRawPositive, shiftForcing, shiftForcingPositive, shiftConstant, shiftOne, shifts⟩ :=
    canonicalExteriorCommonRawSpectralCoordinate_exists_absolute_shift_ball
  have rawPositive := caps.rawPositive
  have physicalPositive := caps.physicalPositive
  have fieldPositive := caps.fieldPositive
  have forcingPositive := caps.forcingPositive
  obtain ⟨areaRadius, areaPositive, _, _, areaEvolution⟩ := diskNormalizedSpectralCoordinate_exists_uniform_evolution
  have normalizedZero : diskNormalizedSpectralCoordinate standardCircleBanach = 0 := by
    simp only [diskNormalizedSpectralCoordinate, contourAreaCentroidNormalization_circle, diskPhysicalSpectralCoordinate_circle]
  have spectralNear : ∀ᶠ data in 𝓝 standardCircleBanach, ‖diskNormalizedSpectralCoordinate data‖ < caps.spectralRadius := by
    have continuous := diskNormalizedSpectralCoordinate_hasLipschitzDerivativeNear_circle.lipschitzNear.continuousAt.norm
    apply continuous.eventually (gt_mem_nhds ?_)
    simpa only [normalizedZero, norm_zero] using caps.spectralPositive
  obtain ⟨spectralPhysicalRadius, spectralPhysicalPositive, spectralInside⟩ := Metric.eventually_nhds_iff.mp spectralNear
  let physicalBudget := min caps.physicalRadius (min caps.fieldRadius (min areaRadius (spectralPhysicalRadius / 2)))
  have physicalBudgetPositive : 0 < physicalBudget := by dsimp only [physicalBudget]; positivity
  obtain ⟨admissibleRadius, admissiblePositive, admissible⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_shift_admissibility physicalBudget physicalBudgetPositive
  obtain ⟨domainRadius, domainPositive, domains⟩ := movingStrainSpectral_exists_relabel_domain
    (show 0 < admissibleRadius / 2 by positivity)
  obtain ⟨inverseRadius, inversePositive, inverses⟩ := Metric.eventually_nhds_iff.mp diskPhysicalSpectralCoordinate_eventually_left_inverse
  let rawRadius := min caps.rawRadius (min shiftRaw (min domainRadius
    (min inverseRadius (admissibleRadius / (1 + ‖diskNeutralCLM‖)))))
  let forcingRadius := min caps.forcingRadius (min shiftForcing admissibleRadius)
  have forcingRadiusPositive : 0 < forcingRadius := by dsimp only [forcingRadius]; positivity
  refine ⟨rawRadius, by dsimp only [rawRadius]; positivity, forcingRadius, forcingRadiusPositive,
    min_le_left _ _, shiftConstant, shiftOne, ?_⟩
  intro count family index state inside area centered frequency time distance weight nonzero positive weightNonnegative
    small separated weightBound forcingSmall
  have stateBound : ‖state‖ ≤ rawRadius := (by simpa only [mem_ball, dist_zero_right] using inside : ‖state‖ < rawRadius).le
  have domain := domains state (ball_subset_ball ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) inside)
  have inverse : diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart state) = state := by
    apply inverses
    simpa only [mem_ball, dist_zero_right] using
      (ball_subset_ball ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) inside :
        state ∈ ball 0 inverseRadius)
  have base := movingStrainSpectral_stationary_base_eq_fixedRelabel state domain.1
  rw [fixedRelabelEquivalence_circle _ domain.1 (diskNeutralCLM_real state)] at base
  have angularSmall : ‖diskNeutralCLM state‖ ≤ admissibleRadius := by
    have scaled := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskNeutralCLM‖)).mp
      (stateBound.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
    nlinarith [diskNeutralCLM.le_opNorm state, norm_nonneg state]
  have totalSmall : ‖diskRelabelCurve (diskNeutralCLM state) 1 - standardCircleBanach‖ +
      ‖diskPhysicalSpectralChart state - diskRelabelCurve (diskNeutralCLM state) 1‖ ≤ admissibleRadius := by
    have baseSmall := domain.2.2.1
    have defectSmall := domain.2.2.2
    simp only [diskPhysicalSpectralDefect, base] at defectSmall
    rw [base] at baseSmall
    linarith
  have scale4 : 4 * (family.patch index).radius ≤ distance := by linarith [(family.patch index).radius_positive]
  have shifted := admissible family index (diskNeutralCLM state)
    (diskPhysicalSpectralChart state - diskRelabelCurve (diskNeutralCLM state) 1)
    angularSmall (diskNeutralCLM_real state) nonzero positive weightNonnegative scale4 separated weightBound
    totalSmall (forcingSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  simp only [add_sub_cancel] at shifted
  have physicalBound : ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time
      (diskPhysicalSpectralChart state) - standardCircleBanach‖ ≤ physicalBudget := by
    with_reducible_and_instances
      simp only [canonicalExteriorCommonPhysicalCoordinate, inverse]
      calc
        _ = ‖(diskPhysicalSpectralChart state - standardCircleBanach) -
            (diskPhysicalSpectralChart state - family.canonicalExteriorAffineCoordinate index (diskNeutralCLM state) frequency time (diskPhysicalSpectralChart state))‖ := by congr 1; abel
        _ ≤ ‖diskPhysicalSpectralChart state - standardCircleBanach‖ +
            ‖diskPhysicalSpectralChart state - family.canonicalExteriorAffineCoordinate index (diskNeutralCLM state) frequency time (diskPhysicalSpectralChart state)‖ := norm_sub_le _ _
        _ ≤ physicalBudget := shifted
  have fieldBound : ‖diskPhysicalSpectralChart state - standardCircleBanach‖ ≤ physicalBudget := by
    linarith [norm_nonneg (diskPhysicalSpectralChart state -
      family.canonicalExteriorAffineCoordinate index (diskNeutralCLM state) frequency time (diskPhysicalSpectralChart state))]
  have spectralBound : ‖family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time
      (diskPhysicalSpectralChart state)‖ ≤ caps.spectralRadius := by
    apply le_of_lt
    apply spectralInside
    rw [dist_eq_norm]
    exact (physicalBound.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))).trans_lt
      (half_lt_self spectralPhysicalPositive)
  have normalizedArea : diskSpectralTubularArea
      (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state)) = Real.pi := by
    have zeroEquation : HasDerivAt (fun _ : ℝ => family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state))
        ((0 : ℝ) • diskEulerRotatingField (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state)) + 0) 0 := by
      simpa only [zero_smul, zero_add] using hasDerivAt_const (0 : ℝ)
        (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state))
    with_reducible_and_instances
      unfold canonicalExteriorCommonNormalizedPhysicalCoordinate
      exact (areaEvolution
        (curve := fun _ => family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state))
        (time := 0) (frequency := 0) (error := 0)
        (physicalBound.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) zeroEquation).1
  have rawShiftInside : state ∈ ball 0 shiftRaw :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) inside
  have shift := by
    with_reducible_and_instances
      exact shifts family index state rawShiftInside area centered nonzero positive weightNonnegative small separated
        weightBound (forcingSmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have coordinateIdentity := by
    with_reducible_and_instances
      exact family.canonicalExteriorCommonRawSpectralCoordinate_eq_normalized_physical_of_inverse index frequency time state inverse
  with_reducible_and_instances rw [coordinateIdentity] at shift
  have projectedShift := by
    with_reducible_and_instances
      exact (diskPhysicalTransverseProjection.le_opNorm
        (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state) - state)).trans
          (mul_le_mul_of_nonneg_left shift (norm_nonneg diskPhysicalTransverseProjection))
  with_reducible_and_instances rw [map_sub] at projectedShift
  have projectedTriangle := by
    with_reducible_and_instances
      exact norm_add_le
        (diskPhysicalTransverseProjection
          (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state) - state))
        (diskPhysicalTransverseProjection state)
  with_reducible_and_instances rw [map_sub, sub_add_cancel] at projectedTriangle
  refine ⟨ball_subset_ball (min_le_left _ _) inside, by simpa only [inverse] using domain.1,
    fieldBound.trans ((min_le_right _ _).trans (min_le_left _ _)), physicalBound.trans (min_le_left _ _),
    spectralBound, normalizedArea, ?_⟩
  with_reducible_and_instances
    exact projectedTriangle.trans ((add_le_add_right projectedShift _).trans_eq (add_comm _ _))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
