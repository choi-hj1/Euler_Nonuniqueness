import EulerNonuniqueness.General.LocalQuadraticVelocityBilinearCubic
import EulerNonuniqueness.General.QuadraticCommutatorOperator

namespace EulerNonuniqueness.General

noncomputable section

open Filter Metric
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace

theorem exists_relative_quadratic_velocity_symmetric_ball
    (neutral : Space →L[ℝ] Space) (transverse velocity : Space → Space)
    (coefficient : Space → BilinearEnd Space) (valid : Space → Prop)
    (regular : LipschitzNear coefficient (0 : Space))
    (relative : ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius → valid initial → valid final →
      ‖velocity initial - velocity final‖ ≤ constant *
        ((‖transverse initial‖ + ‖transverse final‖) * ‖transverse initial - transverse final‖ +
          (‖transverse initial‖ + ‖transverse final‖) ^ 2 * ‖neutral initial - neutral final‖))
    (absolute : ∃ constant ≥ 0, ∀ᶠ state in 𝓝 (0 : Space), valid state →
      ‖velocity state‖ ≤ constant * ‖transverse state‖ ^ 2) :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius → valid initial → valid final →
      ‖(coefficient (neutral initial) (velocity initial) (transverse initial) +
          coefficient (neutral initial) (transverse initial) (velocity initial)) -
        (coefficient (neutral final) (velocity final) (transverse final) +
          coefficient (neutral final) (transverse final) (velocity final))‖ ≤ constant *
        ((‖transverse initial‖ + ‖transverse final‖) ^ 2 * ‖transverse initial - transverse final‖ +
          (‖transverse initial‖ + ‖transverse final‖) ^ 3 * ‖neutral initial - neutral final‖) := by
  have flipRegular : LipschitzNear (fun operator : BilinearEnd Space => operator.flip) (coefficient 0) :=
    lipschitzNear_of_contDiffAt_one (bilinearFlipOperator (Space := Space)).contDiff.contDiffAt
  have flipped := flipRegular.comp regular
  obtain ⟨firstRadius, firstPositive, firstConstant, firstNonnegative, firstBound⟩ :=
    exists_relative_quadratic_velocity_bilinear_ball neutral transverse velocity coefficient valid regular relative absolute
  obtain ⟨secondRadius, secondPositive, secondConstant, secondNonnegative, secondBound⟩ :=
    exists_relative_quadratic_velocity_bilinear_ball neutral transverse velocity
      (fun state => (coefficient state).flip) valid flipped relative absolute
  refine ⟨min firstRadius secondRadius, lt_min firstPositive secondPositive,
    firstConstant + secondConstant, by positivity, ?_⟩
  intro initial final initialInside finalInside initialValid finalValid
  have first := firstBound initial final (ball_subset_ball (min_le_left _ _) initialInside)
    (ball_subset_ball (min_le_left _ _) finalInside) initialValid finalValid
  have second := secondBound initial final (ball_subset_ball (min_le_right _ _) initialInside)
    (ball_subset_ball (min_le_right _ _) finalInside) initialValid finalValid
  have identity (firstInitial secondInitial firstFinal secondFinal : Space) :
      (firstInitial + secondInitial) - (firstFinal + secondFinal) =
        (firstInitial - firstFinal) + (secondInitial - secondFinal) := by abel
  rw [identity]
  exact (norm_add_le _ _).trans ((add_le_add first second).trans_eq (by ring))

end

end EulerNonuniqueness.General
