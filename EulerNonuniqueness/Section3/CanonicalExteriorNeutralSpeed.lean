import EulerNonuniqueness.Section3.CanonicalExteriorNeutralBound
import EulerNonuniqueness.Section3.DiskSpectralSelfBounds
import EulerNonuniqueness.Section3.DiskSpectralAreaAbsorption

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

local instance exteriorNeutralSpeedC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

open EulerNonuniqueness.Section6

theorem canonicalProjectedExteriorContourField_exists_uniform_neutral_speed :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance weight density : ℝ)
        (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
        (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖)
        (weightBound : (∫ position, inverseSquareVorticityWeight
          (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight)
        (phase : Circle) (point : PeriodicC1HolderHalf),
      ‖diskRelabelNeutralCLM point‖ + ‖point - diskRelabelNeutralCLM point‖ ≤ radius →
      diskSpectralTubularArea point = Real.pi →
      ‖density • diskRelabelNeutralCLM (diskSpectralTubularEulerField point) +
        diskRelabelNeutralCLM
          (diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart point)
            (family.canonicalProjectedExteriorContourField index time distance positive
              (by linarith [(family.patch index).radius_positive]) separated phase
              (diskPhysicalSpectralChart point)))‖ ≤
        constant * (|density| * ‖diskPhysicalTransverseProjection point‖ ^ 2 +
          weight * ‖diskPhysicalTransverseProjection point‖) := by
  obtain ⟨forcingRadius, forcingPositive, forcingConstant, forcingOne, forcingBound⟩ :=
    canonicalProjectedExteriorContourField_exists_uniform_neutral_bound
  obtain ⟨selfRadius, selfPositive, _, _, _, _, _, _, selfConstant, selfNonnegative, selfBounds⟩ :=
    diskSpectral_exists_uniform_projected_self_bounds
  obtain ⟨areaRadius, areaPositive, _, _, areaBounds⟩ := diskSpectralTubularArea_exists_transverse_absorption
  let radius := min selfRadius (min forcingRadius (min areaRadius (1 / (‖diskPhysicalTransverseProjection‖ + 1))))
  let constant := selfConstant + 2 * forcingConstant + 1
  have constantOne : 1 ≤ constant := by dsimp [constant]; linarith
  have selfLe : selfConstant ≤ constant := by dsimp [constant]; linarith
  have forcingLe : 2 * forcingConstant ≤ constant := by dsimp [constant]; linarith
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_⟩
  intro count family index time distance weight density positive weightNonnegative small separated weightBound phase point inside area
  have selfInside := inside.trans (min_le_left _ _)
  have forcingInside := inside.trans ((min_le_right _ _).trans (min_le_left _ _))
  have areaInside := inside.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have relativeSmall : ‖point - diskRelabelNeutralCLM point‖ ≤ 1 / (‖diskPhysicalTransverseProjection‖ + 1) :=
    (le_add_of_nonneg_left (norm_nonneg (diskRelabelNeutralCLM point))).trans
      (inside.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have projectedSmall : ‖diskPhysicalTransverseProjection point‖ ≤ 1 := by
    have projected : ‖diskPhysicalTransverseProjection point‖ ≤
        ‖diskPhysicalTransverseProjection‖ * ‖point - diskRelabelNeutralCLM point‖ := by
      rw [← diskSpectralRelative_transverse]
      exact diskPhysicalTransverseProjection.le_opNorm _
    have smallProduct := mul_le_mul_of_nonneg_left relativeSmall (norm_nonneg diskPhysicalTransverseProjection)
    have unitBound : ‖diskPhysicalTransverseProjection‖ * (1 / (‖diskPhysicalTransverseProjection‖ + 1)) ≤ 1 := by
      rw [mul_one_div]
      exact (div_le_one₀ (by positivity)).mpr (by linarith [norm_nonneg diskPhysicalTransverseProjection])
    exact projected.trans (smallProduct.trans unitBound)
  have selfBound := (selfBounds point selfInside area).2.2.2 projectedSmall
  have absorbed := (areaBounds point areaInside area).1
  rw [diskSpectralRelative_transverse] at absorbed
  have forceBound := forcingBound family index time distance weight positive weightNonnegative small
    separated weightBound phase point forcingInside
  calc
    _ ≤ ‖density • diskRelabelNeutralCLM (diskSpectralTubularEulerField point)‖ +
        ‖diskRelabelNeutralCLM
          (diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart point)
            (family.canonicalProjectedExteriorContourField index time distance positive
              (by linarith [(family.patch index).radius_positive]) separated phase
              (diskPhysicalSpectralChart point)))‖ := norm_add_le _ _
    _ ≤ |density| * (selfConstant * ‖diskPhysicalTransverseProjection point‖ ^ 2) +
        forcingConstant * weight * (2 * ‖diskPhysicalTransverseProjection point‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left selfBound (abs_nonneg _))
        (forceBound.trans (mul_le_mul_of_nonneg_left absorbed (by positivity)))
    _ = selfConstant * (|density| * ‖diskPhysicalTransverseProjection point‖ ^ 2) +
        (2 * forcingConstant) * (weight * ‖diskPhysicalTransverseProjection point‖) := by ring
    _ ≤ constant * (|density| * ‖diskPhysicalTransverseProjection point‖ ^ 2) +
        constant * (weight * ‖diskPhysicalTransverseProjection point‖) := by gcongr
    _ = _ := by ring

end EulerNonuniqueness.Paper
