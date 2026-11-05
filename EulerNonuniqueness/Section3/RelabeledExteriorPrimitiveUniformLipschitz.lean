import EulerNonuniqueness.Section3.RelabeledExteriorPrimitiveDifference
import EulerNonuniqueness.Section3.RelabelMapUniformLipschitz

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance relabeledExteriorUniformLipC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

theorem relabeledExteriorForcingPrimitive_exists_uniform_parameter_lipschitz :
    ∃ radius > 0, ∃ constant : NNReal,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (first second : PeriodicC1HolderHalf), ‖first‖ ≤ radius → ‖second‖ ≤ radius →
      (∀ label, star (first.val.1 label) = first.val.1 label) →
      (∀ label, star (second.val.1 label) = second.val.1 label) →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      48 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight →
      ‖family.relabeledExteriorForcingPrimitive index first frequency time -
        family.relabeledExteriorForcingPrimitive index second frequency time‖ ≤
        (48 * constant * weight / (Real.pi * |frequency|)) * ‖first - second‖ := by
  obtain ⟨radius, positiveRadius, constant, bounds, lipschitz⟩ := diskRelabelMap_exists_uniform_lipschitz
  refine ⟨radius, positiveRadius, constant, ?_⟩
  intro count family index first second firstNear secondNear firstReal secondReal
    frequency time distance weight nonzero positive weightNonnegative small separated weightBound
  have ratioBound : 24 * (family.patch index).radius / distance ≤ 1 / 2 :=
    (div_le_iff₀ positive).mpr (by linarith)
  have ratioSmall : 24 * (family.patch index).radius / distance < 1 := by linarith
  have inverseBound : (1 - 24 * (family.patch index).radius / distance)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (one_div_le (by linarith : 0 < 1 - 24 * (family.patch index).radius / distance)
      (by norm_num : (0 : ℝ) < 2)).mpr
    linarith
  have weightedBound :
      (1 - 24 * (family.patch index).radius / distance)⁻¹ *
        (24 * ((∫ position, inverseSquareVorticityWeight
          (family.subfamilyVorticity (Finset.univ.erase index) time)
          ((family.patch index).center time) position) / (2 * Real.pi))) ≤ 24 * weight / Real.pi := by
    have integralNonnegative : 0 ≤ ∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position := by
      apply integral_nonneg
      intro position
      unfold inverseSquareVorticityWeight
      positivity
    calc
      _ ≤ 2 * (24 * (weight / (2 * Real.pi))) :=
        mul_le_mul inverseBound
          (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right weightBound (by positivity)) (by norm_num))
          (by positivity) (by norm_num)
      _ = _ := by ring
  have estimate := family.relabeledExteriorForcingPrimitive_difference_bound index first second
    (bounds first firstNear).1 (bounds second secondNear).1 firstReal secondReal
    (bounds first firstNear).2 (bounds second secondNear).2 nonzero positive ratioSmall separated
  calc
    _ ≤ (2 / |frequency|) * (24 * weight / Real.pi) * (constant * ‖first - second‖) :=
      estimate.trans (mul_le_mul
        (mul_le_mul_of_nonneg_left weightedBound (by positivity))
        (lipschitz first second firstNear secondNear) (norm_nonneg _) (by positivity))
    _ = _ := by ring

end EulerNonuniqueness.Paper
