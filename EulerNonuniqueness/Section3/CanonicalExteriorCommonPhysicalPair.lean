import EulerNonuniqueness.Section3.CanonicalExteriorCommonPhysicalDerivative
import EulerNonuniqueness.Section3.CanonicalExteriorCommonShiftRelative
import EulerNonuniqueness.Section3.DiskTrueAngularPhysicalPairBounds
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

theorem canonicalExteriorCommonPhysicalCoordinate_exists_raw_pair_ball :
    ∃ rawRadius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (first final : PeriodicC1HolderHalf), first ∈ ball 0 rawRadius → final ∈ ball 0 rawRadius →
      diskSpectralTubularArea first = Real.pi → diskSpectralTubularArea final = Real.pi →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      192 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      weight / |frequency| ≤ 1 →
      ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart first) -
        family.canonicalExteriorCommonPhysicalCoordinate index frequency time (diskPhysicalSpectralChart final)‖ ≤
        constant * (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
          ‖diskNeutralCLM first - diskNeutralCLM final‖) := by
  obtain ⟨shiftRadius, shiftPositive, shiftConstant, shiftOne, shifts⟩ :=
    canonicalExteriorAffineCoordinate_exists_common_shift_relative
  obtain ⟨geometryRadius, geometryPositive, geometryConstant, geometryOne, geometry⟩ :=
    diskPhysicalSpectralChart_exists_true_angular_pair_bounds
  obtain ⟨domainRadius, domainPositive, domains⟩ := movingStrainSpectral_exists_relabel_domain (by norm_num : (0 : ℝ) < 1)
  obtain ⟨inverseRadius, inversePositive, inverses⟩ := Metric.eventually_nhds_iff.mp diskPhysicalSpectralCoordinate_eventually_left_inverse
  let rawRadius := min geometryRadius (min domainRadius (min inverseRadius (shiftRadius / (1 + ‖diskNeutralCLM‖))))
  let constant := geometryConstant + shiftConstant * (geometryConstant + 2) + 1
  have geometryNonnegative : 0 ≤ geometryConstant := by linarith
  have shiftNonnegative : 0 ≤ shiftConstant := by linarith
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ shiftConstant * (geometryConstant + 2) := by positivity
    dsimp only [constant]
    linarith
  refine ⟨rawRadius, by dsimp only [rawRadius]; positivity, constant, constantOne, ?_⟩
  intro count family index first final firstInside finalInside firstArea finalArea frequency time distance weight
    nonzero positive weightNonnegative small separated weightBound forcingSmall
  have within {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 rawRadius) :
      diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart state) = state ∧
      ‖diskNeutralCLM state‖ ≤ shiftRadius ∧
      ‖diskPhysicalSpectralChart state - diskRelabelCurve (diskNeutralCLM state) 1‖ ≤ 1 := by
    have stateSmall : ‖state‖ ≤ rawRadius := (by simpa only [mem_ball, dist_zero_right] using inside : ‖state‖ < rawRadius).le
    have domain := domains state (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) inside)
    have base := movingStrainSpectral_stationary_base_eq_fixedRelabel state domain.1
    rw [fixedRelabelEquivalence_circle _ domain.1 (diskNeutralCLM_real state)] at base
    have scaled := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskNeutralCLM‖)).mp
      (stateSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    refine ⟨inverses ?_, ?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right] using
        (ball_subset_ball ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) inside : state ∈ ball 0 inverseRadius)
    · nlinarith [diskNeutralCLM.le_opNorm state, norm_nonneg state]
    · simpa only [diskPhysicalSpectralDefect, base] using domain.2.2.2.le
  have firstWithin := within firstInside
  have finalWithin := within finalInside
  have pair := geometry first final (ball_subset_ball (min_le_left _ _) firstInside)
    (ball_subset_ball (min_le_left _ _) finalInside) firstArea finalArea
  dsimp only at pair
  let transverse := ‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖
  let angular := ‖diskNeutralCLM first - diskNeutralCLM final‖
  have transverseNonnegative : 0 ≤ transverse := norm_nonneg _
  have angularNonnegative : 0 ≤ angular := norm_nonneg _
  have actual := shifts family index (diskNeutralCLM first) (diskNeutralCLM final)
    firstWithin.2.1 finalWithin.2.1 (diskNeutralCLM_real first) (diskNeutralCLM_real final)
    nonzero positive weightNonnegative (by linarith [(family.patch index).radius_positive]) separated weightBound
    (diskPhysicalSpectralChart first) (diskPhysicalSpectralChart final)
  have geometric : ‖diskPhysicalSpectralChart first - diskPhysicalSpectralChart final‖ +
      (1 + ‖diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1‖) * angular ≤
      (geometryConstant + 2) * (transverse + angular) := by
    have bounded := add_le_add pair.2.2.2.2
      (mul_le_mul_of_nonneg_right (show 1 + ‖diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1‖ ≤ 2 by linarith [finalWithin.2.2]) angularNonnegative)
    have leftover : 0 ≤ 2 * transverse := by positivity
    nlinarith only [bounded, leftover]
  have shiftBound := actual.trans (mul_le_mul_of_nonneg_left geometric (by positivity))
  have shiftBoundOne := shiftBound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left forcingSmall shiftNonnegative) (by positivity : 0 ≤ (geometryConstant + 2) * (transverse + angular)))
  have identity : family.canonicalExteriorAffineCoordinate index (diskNeutralCLM first) frequency time (diskPhysicalSpectralChart first) -
      family.canonicalExteriorAffineCoordinate index (diskNeutralCLM final) frequency time (diskPhysicalSpectralChart final) =
      (diskPhysicalSpectralChart first - diskPhysicalSpectralChart final) -
      ((diskPhysicalSpectralChart first - family.canonicalExteriorAffineCoordinate index (diskNeutralCLM first) frequency time (diskPhysicalSpectralChart first)) -
        (diskPhysicalSpectralChart final - family.canonicalExteriorAffineCoordinate index (diskNeutralCLM final) frequency time (diskPhysicalSpectralChart final))) := by abel
  simp only [canonicalExteriorCommonPhysicalCoordinate, firstWithin.1, finalWithin.1]
  rw [identity]
  have bounded := (norm_sub_le _ _).trans (add_le_add pair.2.2.2.2 shiftBoundOne)
  have coefficientLe : geometryConstant + shiftConstant * (geometryConstant + 2) ≤ constant := by dsimp only [constant]; linarith
  have scalar := mul_le_mul_of_nonneg_right coefficientLe (add_nonneg transverseNonnegative angularNonnegative)
  exact (bounded.trans_eq (by ring)).trans scalar

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
