import EulerNonuniqueness.Section3.CanonicalExteriorCommonRawCoordinateComparison

noncomputable section

open Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorCommonRawSpectralCoordinate_exists_absolute_shift_ball :
    ∃ rawRadius > 0, ∃ forcingRadius > 0, ∃ constant ≥ 1,
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
      ‖family.canonicalExteriorCommonRawSpectralCoordinate index frequency time state - state‖ ≤
        constant * (weight / |frequency|) := by
  obtain ⟨shiftRadius, shiftPositive, shiftConstant, shiftOne, shifts⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_near_identity_bound
  obtain ⟨chartRadius, chartPositive, chartConstant, chartOne, charts, _⟩ :=
    diskPhysicalSpectralChart_exists_uniform_firstOrder_bounds
  obtain ⟨inverseRadius, inversePositive, inverses⟩ := diskNormalizedSpectralCoordinate_exists_constraints_left_inverse
  obtain ⟨domainRadius, domainPositive, domains⟩ := movingStrainSpectral_exists_relabel_domain (by norm_num : (0 : ℝ) < 1)
  obtain ⟨normalConstant, normalNeighborhood, normalNear, normalLip⟩ :=
    diskNormalizedSpectralCoordinate_hasLipschitzDerivativeNear_circle.lipschitzNear
  obtain ⟨normalRadius, normalPositive, normalContained⟩ := Metric.mem_nhds_iff.mp normalNear
  let rawRadius := min inverseRadius (min chartRadius (min domainRadius
    (min (shiftRadius / (1 + ‖diskNeutralCLM‖)) (normalRadius / (4 * chartConstant)))))
  let forcingRadius := normalRadius / (8 * shiftConstant)
  let constant := 2 * (normalConstant : ℝ) * shiftConstant + 1
  have chartConstantPositive : 0 < chartConstant := by linarith
  have shiftConstantPositive : 0 < shiftConstant := by linarith
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ 2 * (normalConstant : ℝ) * shiftConstant := by positivity
    dsimp only [constant]
    linarith
  refine ⟨rawRadius, by dsimp only [rawRadius]; positivity, forcingRadius, by dsimp only [forcingRadius]; positivity,
    constant, constantOne, ?_⟩
  intro count family index state inside area centered frequency time distance weight nonzero positive weightNonnegative small separated weightBound forcingSmall
  have stateSmall : ‖state‖ ≤ rawRadius := (by simpa only [mem_ball, dist_zero_right] using inside : ‖state‖ < rawRadius).le
  have domain := domains state (ball_subset_ball ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) inside)
  have base := movingStrainSpectral_stationary_base_eq_fixedRelabel state domain.1
  rw [fixedRelabelEquivalence_circle _ domain.1 (diskNeutralCLM_real state)] at base
  have defect : ‖diskPhysicalSpectralChart state - diskRelabelCurve (diskNeutralCLM state) 1‖ ≤ 1 := by
    simpa only [diskPhysicalSpectralDefect, base] using domain.2.2.2.le
  have angularSmall : ‖diskNeutralCLM state‖ ≤ shiftRadius := by
    have scaled := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskNeutralCLM‖)).mp
      (stateSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
    nlinarith [diskNeutralCLM.le_opNorm state, norm_nonneg state]
  have rawNear : ‖diskPhysicalSpectralChart state - standardCircleBanach‖ ≤ normalRadius / 4 := by
    have actual := (charts state (stateSmall.trans ((min_le_right _ _).trans (min_le_left _ _)))).1
    have scaled := (le_div_iff₀ (by positivity : 0 < 4 * chartConstant)).mp
      (stateSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
    nlinarith
  have shift := shifts family index (diskNeutralCLM state) angularSmall (diskNeutralCLM_real state)
    nonzero positive weightNonnegative (by linarith [(family.patch index).radius_positive]) separated weightBound (diskPhysicalSpectralChart state)
  have shiftBound : ‖family.canonicalExteriorAffineCoordinate index (diskNeutralCLM state) frequency time (diskPhysicalSpectralChart state) -
      diskPhysicalSpectralChart state‖ ≤ 2 * shiftConstant * (weight / |frequency|) := by
    have actual := shift.trans (mul_le_mul_of_nonneg_left (show 1 + ‖diskPhysicalSpectralChart state - diskRelabelCurve (diskNeutralCLM state) 1‖ ≤ 2 by linarith)
      (by positivity : 0 ≤ shiftConstant * (weight / |frequency|)))
    exact actual.trans_eq (by ring)
  have shiftSmall : ‖family.canonicalExteriorAffineCoordinate index (diskNeutralCLM state) frequency time (diskPhysicalSpectralChart state) -
      diskPhysicalSpectralChart state‖ ≤ normalRadius / 4 := by
    have scaled := (le_div_iff₀ (by positivity : 0 < 8 * shiftConstant)).mp forcingSmall
    linarith
  have correctedNear : ‖family.canonicalExteriorAffineCoordinate index (diskNeutralCLM state) frequency time (diskPhysicalSpectralChart state) - standardCircleBanach‖ < normalRadius := by
    have triangle := norm_sub_le (family.canonicalExteriorAffineCoordinate index (diskNeutralCLM state) frequency time (diskPhysicalSpectralChart state))
      (diskPhysicalSpectralChart state)
    have identity := norm_add_le
      (family.canonicalExteriorAffineCoordinate index (diskNeutralCLM state) frequency time (diskPhysicalSpectralChart state) - diskPhysicalSpectralChart state)
      (diskPhysicalSpectralChart state - standardCircleBanach)
    rw [sub_add_sub_cancel] at identity
    linarith
  have inverse := inverses state ((by simpa only [mem_ball, dist_zero_right] using inside : ‖state‖ < rawRadius).trans_le (min_le_left _ _)) area centered
  have firstMember := normalContained (show family.canonicalExteriorAffineCoordinate index (diskNeutralCLM state) frequency time (diskPhysicalSpectralChart state) ∈ ball standardCircleBanach normalRadius by
    simpa only [mem_ball, dist_eq_norm] using correctedNear)
  have finalMember := normalContained (show diskPhysicalSpectralChart state ∈ ball standardCircleBanach normalRadius by
    rw [mem_ball, dist_eq_norm]
    exact rawNear.trans_lt (by linarith))
  have actual := (normalLip.norm_sub_le firstMember finalMember).trans
    (mul_le_mul_of_nonneg_left shiftBound normalConstant.coe_nonneg)
  rw [inverse] at actual
  have coefficientLe : 2 * (normalConstant : ℝ) * shiftConstant ≤ constant := by dsimp only [constant]; linarith
  have scalar := mul_le_mul_of_nonneg_right coefficientLe (by positivity : 0 ≤ weight / |frequency|)
  with_reducible_and_instances
    unfold canonicalExteriorCommonRawSpectralCoordinate canonicalExteriorCommonNormalizedCoordinate
    calc
      _ ≤ (normalConstant : ℝ) * (2 * shiftConstant * (weight / |frequency|)) := actual
      _ = (2 * (normalConstant : ℝ) * shiftConstant) * (weight / |frequency|) := by ring
      _ ≤ constant * (weight / |frequency|) := scalar

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
