import EulerNonuniqueness.Section3.DiskTrueAngularNeutralRelative
import EulerNonuniqueness.Section3.DiskNormalizedSpectralRelativeError
import EulerNonuniqueness.Section3.CanonicalExteriorValueBound
import EulerNonuniqueness.Section3.CanonicalExteriorDifference
import EulerNonuniqueness.General.AffineResidualRelativeRemainder

noncomputable section

open Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalProjectedExteriorContourField_exists_true_angular_drift_relative_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (firstData finalData : PeriodicC1HolderHalf),
      ‖firstData - standardCircleBanach‖ ≤ radius → ‖finalData - standardCircleBanach‖ ≤ radius →
      contourAreaFunctional firstData = Real.pi → contourAreaFunctional finalData = Real.pi →
      ∀ (time distance weight frequency : ℝ) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
        (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖),
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      ∀ phase : Circle,
      let force := family.canonicalProjectedExteriorContourField index time distance positive
        (by linarith [(family.patch index).radius_positive]) separated phase
      let first := diskPhysicalSpectralCoordinate firstData
      let final := diskPhysicalSpectralCoordinate finalData
      ‖diskNeutralCLM (diskPhysicalSpectralInverseDerivative firstData
          (frequency • diskEulerRotatingField firstData + force firstData)) -
        diskNeutralCLM (diskPhysicalSpectralInverseDerivative finalData
          (frequency • diskEulerRotatingField finalData + force finalData))‖ ≤ constant *
        (|frequency| *
          ((‖diskPhysicalTransverseProjection first‖ + ‖diskPhysicalTransverseProjection final‖) *
              ‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
            (‖diskPhysicalTransverseProjection first‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2 *
              ‖diskNeutralCLM first - diskNeutralCLM final‖) + weight * ‖firstData - finalData‖) := by
  obtain ⟨selfRadius, selfPositive, selfConstant, selfNonnegative, selfRelative⟩ :=
    diskSpectralTrueAngularField_exists_relative_quadratic_ball
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverseAbsolute, inverseRelative⟩ :=
    diskPhysicalSpectralInverseDerivative_exists_uniform_pair_bounds
  obtain ⟨valueRadius, valuePositive, _, valueConstant, valueOne, values⟩ :=
    canonicalProjectedExteriorContourField_exists_uniform_value_bound
  obtain ⟨differenceRadius, differencePositive, _, differenceConstant, differenceOne, differences⟩ :=
    canonicalProjectedExteriorContourField_exists_uniform_difference_bound
  have coordinateSmall : ∀ᶠ data in 𝓝 standardCircleBanach,
      diskPhysicalSpectralCoordinate data ∈ ball 0 selfRadius := by
    have limit := diskPhysicalSpectralCoordinate_continuousAt_circle.tendsto
    rw [diskPhysicalSpectralCoordinate_circle] at limit
    exact limit.eventually (ball_mem_nhds _ selfPositive)
  obtain ⟨validRadius, validPositive, valid⟩ := Metric.eventually_nhds_iff.mp
    (diskPhysicalSpectralCoordinate_eventually_inverse_derivative.and
      (diskPhysicalSpectralCoordinate_eventually_area.and coordinateSmall))
  let radius := min inverseRadius (min valueRadius (min differenceRadius (validRadius / 2)))
  let forceConstant := valueConstant + differenceConstant
  let constant := selfConstant + 2 * ‖diskNeutralCLM‖ * inverseConstant * forceConstant + 1
  have forceNonnegative : 0 ≤ forceConstant := by dsimp only [forceConstant]; linarith
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ 2 * ‖diskNeutralCLM‖ * inverseConstant * forceConstant := by positivity
    dsimp only [constant]
    linarith
  refine ⟨radius, by dsimp only [radius]; positivity, constant, constantOne, ?_⟩
  intro count family index firstData finalData firstInside finalInside firstArea finalArea
    time distance weight frequency positive weightNonnegative small separated weightBound phase
  dsimp only
  have within {data : PeriodicC1HolderHalf} (inside : ‖data - standardCircleBanach‖ ≤ radius) :
      ‖data - standardCircleBanach‖ ≤ inverseRadius ∧ ‖data - standardCircleBanach‖ ≤ valueRadius ∧
        ‖data - standardCircleBanach‖ ≤ differenceRadius ∧ dist data standardCircleBanach < validRadius := by
    refine ⟨inside.trans (min_le_left _ _), inside.trans ((min_le_right _ _).trans (min_le_left _ _)),
      inside.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))), ?_⟩
    rw [dist_eq_norm]
    exact (inside.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))).trans_lt (by linarith)
  have firstWithin := within firstInside
  have finalWithin := within finalInside
  have firstActual := valid firstWithin.2.2.2
  have finalActual := valid finalWithin.2.2.2
  let force := family.canonicalProjectedExteriorContourField index time distance positive
    (by linarith [(family.patch index).radius_positive]) separated phase
  have forcePair : ‖force firstData - force finalData‖ ≤ forceConstant * weight * ‖firstData - finalData‖ := by
    have actual := differences family index time distance weight positive weightNonnegative small separated weightBound phase
      (firstData - standardCircleBanach) (finalData - standardCircleBanach) firstWithin.2.2.1 finalWithin.2.2.1
    simp only [add_sub_cancel, sub_sub_sub_cancel_right] at actual
    exact actual.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp only [forceConstant]; linarith : differenceConstant ≤ forceConstant)
        weightNonnegative) (norm_nonneg _))
  have forceValue : ‖force finalData‖ ≤ forceConstant * weight := by
    have actual := values family index time distance weight positive weightNonnegative
      (by linarith [(family.patch index).radius_positive]) separated weightBound phase
      (finalData - standardCircleBanach) finalWithin.2.1
    simp only [add_sub_cancel] at actual
    exact actual.trans (mul_le_mul_of_nonneg_right
      (by dsimp only [forceConstant]; linarith : valueConstant ≤ forceConstant) weightNonnegative)
  have inversePair := inverseRelative firstData finalData firstWithin.1 finalWithin.1
  have applied := EulerNonuniqueness.General.norm_operator_apply_difference_le
    (diskPhysicalSpectralInverseDerivative firstData) (diskPhysicalSpectralInverseDerivative finalData)
    (force firstData) (force finalData)
  have forcingBound : ‖diskPhysicalSpectralInverseDerivative firstData (force firstData) -
      diskPhysicalSpectralInverseDerivative finalData (force finalData)‖ ≤
      2 * inverseConstant * forceConstant * weight * ‖firstData - finalData‖ := by
    have actual := applied.trans (add_le_add
      (mul_le_mul (inverseAbsolute firstData firstWithin.1) forcePair (norm_nonneg _) (by linarith))
      (mul_le_mul inversePair forceValue (norm_nonneg _) (by positivity)))
    exact actual.trans_eq (by ring)
  have selfBound := selfRelative (diskPhysicalSpectralCoordinate firstData) (diskPhysicalSpectralCoordinate finalData)
    firstActual.2.2 finalActual.2.2 (firstActual.2.1.trans firstArea) (finalActual.2.1.trans finalArea)
  have identity :
      diskNeutralCLM (diskPhysicalSpectralInverseDerivative firstData
        (frequency • diskEulerRotatingField firstData + force firstData)) -
      diskNeutralCLM (diskPhysicalSpectralInverseDerivative finalData
        (frequency • diskEulerRotatingField finalData + force finalData)) =
      frequency • (diskNeutralCLM (diskSpectralTubularEulerField (diskPhysicalSpectralCoordinate firstData)) -
        diskNeutralCLM (diskSpectralTubularEulerField (diskPhysicalSpectralCoordinate finalData))) +
      diskNeutralCLM (diskPhysicalSpectralInverseDerivative firstData (force firstData) -
        diskPhysicalSpectralInverseDerivative finalData (force finalData)) := by
    simp only [map_add, map_smul, map_sub, firstActual.1.2.2, finalActual.1.2.2, smul_sub]
    abel
  change ‖diskNeutralCLM (diskPhysicalSpectralInverseDerivative firstData
    (frequency • diskEulerRotatingField firstData + force firstData)) -
      diskNeutralCLM (diskPhysicalSpectralInverseDerivative finalData
        (frequency • diskEulerRotatingField finalData + force finalData))‖ ≤ _
  rw [identity]
  have angularBound := (diskNeutralCLM.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left forcingBound (norm_nonneg diskNeutralCLM))
  have scaledSelf := mul_le_mul_of_nonneg_left selfBound (abs_nonneg frequency)
  rw [← Real.norm_eq_abs frequency, ← norm_smul] at scaledSelf
  have total := (norm_add_le _ _).trans (add_le_add scaledSelf angularBound)
  apply total.trans
  have selfLe : selfConstant ≤ constant := by
    have nonnegative : 0 ≤ 2 * ‖diskNeutralCLM‖ * inverseConstant * forceConstant := by positivity
    dsimp only [constant]
    linarith
  have sourceLe : 2 * ‖diskNeutralCLM‖ * inverseConstant * forceConstant ≤ constant := by
    dsimp only [constant]
    linarith
  have selfScalar := mul_le_mul_of_nonneg_right selfLe (by positivity : 0 ≤ |frequency| *
    ((‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate firstData)‖ +
        ‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate finalData)‖) *
      ‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate firstData) -
        diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate finalData)‖ +
      (‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate firstData)‖ +
        ‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate finalData)‖) ^ 2 *
        ‖diskNeutralCLM (diskPhysicalSpectralCoordinate firstData) - diskNeutralCLM (diskPhysicalSpectralCoordinate finalData)‖))
  have sourceScalar := mul_le_mul_of_nonneg_right sourceLe
    (mul_nonneg weightNonnegative (norm_nonneg (firstData - finalData)))
  convert add_le_add selfScalar sourceScalar using 1 <;> (try simp only [Real.norm_eq_abs]) <;> ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
