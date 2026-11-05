import EulerNonuniqueness.Section3.CanonicalExteriorNeutralCancellation
import EulerNonuniqueness.Section3.CanonicalExteriorDifference
import EulerNonuniqueness.Section3.CanonicalExteriorValueBound
import EulerNonuniqueness.Section3.DiskPhysicalSpectralFirstOrderBounds
import EulerNonuniqueness.General.ProjectedOperatorDifference

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance exteriorNeutralBoundC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

open EulerNonuniqueness.Section6

theorem canonicalProjectedExteriorContourField_exists_uniform_neutral_bound :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance weight : ℝ)
        (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
        (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖)
        (weightBound : (∫ position, inverseSquareVorticityWeight
          (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight)
        (phase : Circle) (point : PeriodicC1HolderHalf),
      ‖diskRelabelNeutralCLM point‖ + ‖point - diskRelabelNeutralCLM point‖ ≤ radius →
      ‖diskRelabelNeutralCLM
        (diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart point)
          (family.canonicalProjectedExteriorContourField index time distance positive
            (by linarith [(family.patch index).radius_positive]) separated phase
            (diskPhysicalSpectralChart point)))‖ ≤
        constant * weight * ‖point - diskRelabelNeutralCLM point‖ := by
  obtain ⟨chartRadius, chartPositive, chartConstant, chartOne, chartBounds, chartDifference⟩ :=
    diskPhysicalSpectralChart_exists_uniform_firstOrder_bounds
  obtain ⟨valueRadius, valuePositive, _, valueConstant, valueOne, valueBounds⟩ :=
    FiniteMovingPatchFamily.canonicalProjectedExteriorContourField_exists_uniform_value_bound
  obtain ⟨differenceRadius, differencePositive, _, differenceConstant, differenceOne, differenceBounds⟩ :=
    FiniteMovingPatchFamily.canonicalProjectedExteriorContourField_exists_uniform_difference_bound
  obtain ⟨cancellationRadius, cancellationPositive, cancellation⟩ := Metric.eventually_nhds_iff.mp
    canonicalProjectedExteriorContourField_eventually_neutral_cancellation
  let radius := min (chartRadius / 2)
    (min (cancellationRadius / 2) (min valueRadius differenceRadius / (chartConstant + 1)))
  let bound := chartConstant + valueConstant + differenceConstant * chartConstant + 1
  let constant := 2 * ‖diskRelabelNeutralCLM‖ * bound ^ 2 + 1
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  have radiusChart : radius ≤ chartRadius := (min_le_left _ _).trans (by linarith)
  have radiusCancellation : radius < cancellationRadius :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have physicalBudget : chartConstant * radius ≤ min valueRadius differenceRadius := by
    have raw : radius ≤ min valueRadius differenceRadius / (chartConstant + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have product := (le_div_iff₀ (by linarith : 0 < chartConstant + 1)).mp raw
    nlinarith [radiusPositive]
  have boundNonnegative : 0 ≤ bound := by dsimp [bound]; positivity
  have chartLe : chartConstant ≤ bound := by dsimp [bound]; nlinarith
  have valueLe : valueConstant ≤ bound := by dsimp [bound]; nlinarith
  have differenceLe : differenceConstant * chartConstant ≤ bound := by dsimp [bound]; linarith
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ 2 * ‖diskRelabelNeutralCLM‖ * bound ^ 2 := by positivity
    dsimp [constant]
    linarith
  refine ⟨radius, radiusPositive, constant, constantOne, ?_⟩
  intro count family index time distance weight positive weightNonnegative small separated weightBound phase point inside
  let neutral := diskRelabelNeutralCLM point
  have neutralBound : ‖neutral‖ ≤ radius :=
    (le_add_of_nonneg_right (norm_nonneg (point - diskRelabelNeutralCLM point))).trans inside
  have pointBound : ‖point‖ ≤ radius := by
    have triangle := norm_add_le (diskRelabelNeutralCLM point) (point - diskRelabelNeutralCLM point)
    have identity : diskRelabelNeutralCLM point + (point - diskRelabelNeutralCLM point) = point := by abel
    rw [identity] at triangle
    exact triangle.trans inside
  have neutralChart := chartBounds neutral (neutralBound.trans radiusChart)
  have pointChart := chartBounds point (pointBound.trans radiusChart)
  have physicalBound (current : PeriodicC1HolderHalf) (currentBound : ‖current‖ ≤ radius) :
      ‖diskPhysicalSpectralChart current - standardCircleBanach‖ ≤ min valueRadius differenceRadius :=
    ((chartBounds current (currentBound.trans radiusChart)).1.trans
      (mul_le_mul_of_nonneg_left currentBound (by linarith))).trans physicalBudget
  have neutralPhysical := physicalBound neutral neutralBound
  have pointPhysical := physicalBound point pointBound
  have reconstruct (current : PeriodicC1HolderHalf) :
      standardCircleBanach + (diskPhysicalSpectralChart current - standardCircleBanach) =
        diskPhysicalSpectralChart current := by abel
  have small48 : 48 * (family.patch index).radius ≤ distance := by linarith [(family.patch index).radius_positive]
  have small8 : 8 * (family.patch index).radius ≤ distance := by linarith [(family.patch index).radius_positive]
  have ratio : 24 * (family.patch index).radius / distance < 1 :=
    (div_lt_one positive).mpr (by linarith [(family.patch index).radius_positive])
  have zero := cancellation
    (by simpa only [dist_eq_norm, sub_zero] using neutralBound.trans_lt radiusCancellation)
    (diskRelabelNeutralCLM_idempotent point) family index time distance positive small8 separated ratio phase
  have valueBound := valueBounds family index time distance weight positive weightNonnegative
    small48 separated weightBound phase (diskPhysicalSpectralChart neutral - standardCircleBanach)
    (neutralPhysical.trans (min_le_left _ _))
  rw [reconstruct] at valueBound
  have differenceBound := differenceBounds family index time distance weight positive weightNonnegative
    small separated weightBound phase (diskPhysicalSpectralChart point - standardCircleBanach)
    (diskPhysicalSpectralChart neutral - standardCircleBanach)
    (pointPhysical.trans (min_le_right _ _)) (neutralPhysical.trans (min_le_right _ _))
  rw [reconstruct, reconstruct, sub_sub_sub_cancel_right] at differenceBound
  have chartDifferenceBound := chartDifference point neutral
    (pointBound.trans radiusChart) (neutralBound.trans radiusChart)
  have amplifiedDifference :
      ‖family.canonicalProjectedExteriorContourField index time distance positive small8 separated phase
          (diskPhysicalSpectralChart point) -
        family.canonicalProjectedExteriorContourField index time distance positive small8 separated phase
          (diskPhysicalSpectralChart neutral)‖ ≤ bound * weight * ‖point - neutral‖ := by
    calc
      _ ≤ differenceConstant * weight * (chartConstant * ‖point - neutral‖) := by
        exact differenceBound.trans (mul_le_mul_of_nonneg_left chartDifferenceBound.1 (by positivity))
      _ = (differenceConstant * chartConstant) * weight * ‖point - neutral‖ := by ring
      _ ≤ _ := by gcongr
  have inverseDifference :
      ‖diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart point) -
        diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart neutral)‖ ≤ bound * ‖point - neutral‖ :=
    chartDifferenceBound.2.trans (mul_le_mul_of_nonneg_right chartLe (norm_nonneg _))
  have actual := EulerNonuniqueness.General.norm_projected_operator_value_le_of_base_zero
    diskRelabelNeutralCLM
    (diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart point))
    (diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart neutral))
    (family.canonicalProjectedExteriorContourField index time distance positive small8 separated phase
      (diskPhysicalSpectralChart point))
    (family.canonicalProjectedExteriorContourField index time distance positive small8 separated phase
      (diskPhysicalSpectralChart neutral))
    boundNonnegative weightNonnegative (norm_nonneg (point - neutral)) zero
    (pointChart.2.trans chartLe) inverseDifference
    (valueBound.trans (mul_le_mul_of_nonneg_right valueLe weightNonnegative)) amplifiedDifference
  exact actual.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (show 2 * ‖diskRelabelNeutralCLM‖ * bound ^ 2 ≤ constant by dsimp [constant]; linarith)
      weightNonnegative) (norm_nonneg _))

end EulerNonuniqueness.Paper
