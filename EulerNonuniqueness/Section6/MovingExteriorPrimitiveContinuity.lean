import EulerNonuniqueness.Section3.DiskForcingPrimitiveContinuity
import EulerNonuniqueness.Section6.MovingInversePowerRegularity
import EulerNonuniqueness.Section6.MovingExteriorPrimitiveBound
import EulerNonuniqueness.Section6.UniformExteriorCoefficientBounds

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance geometricPrimitiveContinuityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

theorem exteriorTaylorCoefficient_contDiffAt_of_center_gaps {count : ℕ}
    (family : FiniteMovingPatchFamily count) (power : ℕ)
    (receiver : Fin count) {time distance : ℝ} (positive : 0 < distance)
    (inside : ∀ source ∈ Finset.univ.erase receiver,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (centerGaps : ∀ source ∈ Finset.univ.erase receiver,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch receiver).center time - (family.patch source).center time‖) :
    ContDiffAt ℝ 1 (family.exteriorTaylorCoefficient (Finset.univ.erase receiver)
      (family.patch receiver).center (family.patch receiver).radius power) time := by
  have centerSmooth : ContDiffAt ℝ 1 (family.patch receiver).center time := by
    apply contDiffAt_one_iff.mpr
    refine ⟨fun current => (1 : ℝ →L[ℝ] ℝ).smulRight ((family.patch receiver).centerVelocity current),
      univ, Filter.univ_mem, ?_, ?_⟩
    · exact (((ContinuousLinearMap.smulRightL ℝ ℝ ℂ) 1).continuous.comp
        (family.patch receiver).centerVelocity_continuous).continuousOn
    · intro current _
      exact ((family.patch receiver).center_equation current).hasFDerivAt
  apply family.exteriorTaylorCoefficient_contDiffAt_of_local_center (Finset.univ.erase receiver)
    (family.patch receiver).center (family.patch receiver).radius power centerSmooth inside
    (fun _ => distance) (fun _ _ => positive)
  exact (eventually_all_finset (Finset.univ.erase receiver)).mpr
    (fun source member => (family.patch source).eventually_domain_separated_of_center_gap
      (family.patch receiver).center_continuous (centerGaps source member))

theorem exteriorForcingPrimitive_continuousAt_geometric {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count)
    {frequency time distance weight : ℝ} (nonzero : frequency ≠ 0)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (small : 2 * (family.patch index).radius / distance < 1)
    (inside : ∀ source ∈ Finset.univ.erase index,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (centerGaps : ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center time - (family.patch source).center time‖)
    (weightBound : ∀ᶠ current in 𝓝 time, (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) current)
      ((family.patch index).center current) position) ≤ weight) :
    ContinuousAt (family.exteriorForcingPrimitive index frequency) time := by
  let amplitude := fun power => family.exteriorTaylorCoefficient (Finset.univ.erase index)
    (family.patch index).center (family.patch index).radius (power + 1)
  let bound := fun power : ℕ => ((family.patch index).radius / distance) ^ power * (weight / (2 * Real.pi))
  have weighted : Summable (fun power => (2 : ℝ) ^ (power + 1) * bound power) := by
    have geometric := (summable_geometric_of_lt_one
      (div_nonneg (mul_nonneg (by norm_num) (family.patch index).radius_positive.le) positive.le) small).mul_right
      (2 * (weight / (2 * Real.pi)))
    convert geometric using 1
    funext power
    dsimp only [bound]
    rw [show 2 * (family.patch index).radius / distance = 2 * ((family.patch index).radius / distance) by ring,
      mul_pow, pow_succ]
    ring
  have separatedNear : ∀ᶠ current in 𝓝 time, ∀ source ∈ Finset.univ.erase index,
      ∀ position ∈ (family.patch source).domain current,
        distance ≤ ‖(family.patch index).center current - position‖ :=
    (eventually_all_finset (Finset.univ.erase index)).mpr
      (fun source member => (family.patch source).eventually_domain_separated_of_center_gap
        (family.patch index).center_continuous (centerGaps source member))
  apply diskForcingPrimitive_tsum_continuousAt_of_weighted_bound nonzero amplitude bound
    (fun power => (family.exteriorTaylorCoefficient_contDiffAt_of_center_gaps (power + 1)
      index positive inside centerGaps).continuousAt) weighted
  filter_upwards [separatedNear, weightBound] with current separated bounded
  exact fun power => family.norm_exteriorTaylorCoefficient_le_uniform index positive separated bounded power

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
