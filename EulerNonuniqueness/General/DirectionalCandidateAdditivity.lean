import Mathlib

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℂ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℂ Target]

def directionalCandidateError (function : Domain → Target)
    (candidate : Domain → Domain → Target) (point increment : Domain) : Target :=
  function (point + increment) - function point - candidate point increment

theorem directionalCandidate_additivity_identity
    (function : Domain → Target) (candidate : Domain → Domain → Target)
    (point first second : Domain) (parameter : ℂ)
    (homogeneous : ∀ base direction, candidate base (parameter • direction) =
      parameter • candidate base direction) :
    parameter • (candidate point (first + second) - candidate point first - candidate point second) =
      directionalCandidateError function candidate point (parameter • first) +
        directionalCandidateError function candidate (point + parameter • first) (parameter • second) -
        directionalCandidateError function candidate point (parameter • (first + second)) +
        parameter • (candidate (point + parameter • first) second - candidate point second) := by
  have coordinate : point + parameter • (first + second) =
      (point + parameter • first) + parameter • second := by module
  simp only [directionalCandidateError, homogeneous, coordinate, smul_sub]
  module

theorem directionalCandidate_additivity_defect_bound
    (function : Domain → Target) (candidate : Domain → Domain → Target)
    (point first second : Domain) {parameter : ℂ} {remainderConstant variationConstant : ℝ}
    (nonzero : parameter ≠ 0)
    (homogeneous : ∀ base direction, candidate base (parameter • direction) =
      parameter • candidate base direction)
    (firstBound : ‖directionalCandidateError function candidate point (parameter • first)‖ ≤
      remainderConstant * ‖parameter • first‖ ^ 2)
    (secondBound : ‖directionalCandidateError function candidate
      (point + parameter • first) (parameter • second)‖ ≤
        remainderConstant * ‖parameter • second‖ ^ 2)
    (sumBound : ‖directionalCandidateError function candidate point (parameter • (first + second))‖ ≤
      remainderConstant * ‖parameter • (first + second)‖ ^ 2)
    (variation : ‖candidate (point + parameter • first) second - candidate point second‖ ≤
      variationConstant * ‖parameter • first‖ * ‖second‖) :
    ‖candidate point (first + second) - candidate point first - candidate point second‖ ≤
      (remainderConstant * (‖first‖ ^ 2 + ‖second‖ ^ 2 + ‖first + second‖ ^ 2) +
        variationConstant * ‖first‖ * ‖second‖) * ‖parameter‖ := by
  have scaled := norm_add_le
    (directionalCandidateError function candidate point (parameter • first) +
      directionalCandidateError function candidate (point + parameter • first) (parameter • second) -
      directionalCandidateError function candidate point (parameter • (first + second)))
    (parameter • (candidate (point + parameter • first) second - candidate point second))
  rw [← directionalCandidate_additivity_identity function candidate point first second parameter homogeneous,
    norm_smul] at scaled
  have remainderBound := (norm_sub_le
    (directionalCandidateError function candidate point (parameter • first) +
      directionalCandidateError function candidate (point + parameter • first) (parameter • second))
    (directionalCandidateError function candidate point (parameter • (first + second)))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  have bound := scaled.trans (add_le_add remainderBound le_rfl)
  have controlled := bound.trans
    (add_le_add (add_le_add (add_le_add firstBound secondBound) sumBound)
      (by simpa only [norm_smul] using mul_le_mul_of_nonneg_left variation (norm_nonneg parameter)))
  simp only [norm_smul, mul_pow] at controlled
  have positive : 0 < ‖parameter‖ := norm_pos_iff.mpr nonzero
  apply (mul_le_mul_left positive).mp
  exact controlled.trans_eq (by ring)

theorem directionalCandidate_add_of_vanishing_defect
    (candidate : Domain → Domain → Target) (point first second : Domain) {constant : ℝ}
    (bound : ∀ᶠ parameter in 𝓝[≠] (0 : ℂ),
      ‖candidate point (first + second) - candidate point first - candidate point second‖ ≤
        constant * ‖parameter‖) :
    candidate point (first + second) = candidate point first + candidate point second := by
  have continuous : Continuous (fun parameter : ℂ => constant * ‖parameter‖) :=
    continuous_const.mul continuous_norm
  have vanishes : Tendsto (fun parameter : ℂ => constant * ‖parameter‖)
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa using (continuous.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have nonpositive : ‖candidate point (first + second) - candidate point first - candidate point second‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds vanishes bound
  have zero : candidate point (first + second) - candidate point first - candidate point second = 0 :=
    norm_eq_zero.mp (le_antisymm nonpositive (norm_nonneg _))
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp zero)).trans (add_comm _ _)

end EulerNonuniqueness.General
