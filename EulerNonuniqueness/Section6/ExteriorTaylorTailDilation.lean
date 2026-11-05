import EulerNonuniqueness.General.WeightedTailDilation
import EulerNonuniqueness.Section6.MovingExteriorTaylorCoefficient

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem exteriorTaylorCoefficient_radius_mul {count : ℕ} (family : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (center : ℝ → ℂ) (radius ratio : ℝ) (power : ℕ) (time : ℝ) :
    family.exteriorTaylorCoefficient selected center (ratio * radius) (power + 1) time =
      ratio ^ power • family.exteriorTaylorCoefficient selected center radius (power + 1) time := by
  unfold exteriorTaylorCoefficient
  simp only [Nat.add_sub_cancel, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_mul, mul_pow]
  ring

theorem exteriorTaylorCoefficient_weighted_tail_dilation {count : ℕ}
    (first second : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (firstCenter secondCenter : ℝ → ℂ) (radius ratio time : ℝ) {weight : ℝ}
    (weightNonnegative : 0 ≤ weight) (ratioNonnegative : 0 ≤ ratio) (ratioSmall : ratio ≤ 1)
    (summable : Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient selected firstCenter radius (power + 1) time -
        second.exteriorTaylorCoefficient selected secondCenter radius (power + 1) time‖)) :
    Summable (fun power : ℕ => weight ^ (power + 1) * ‖if power = 0 then 0 else
      first.exteriorTaylorCoefficient selected firstCenter (ratio * radius) (power + 1) time -
        second.exteriorTaylorCoefficient selected secondCenter (ratio * radius) (power + 1) time‖) ∧
      (∑' power : ℕ, weight ^ (power + 1) * ‖if power = 0 then 0 else
        first.exteriorTaylorCoefficient selected firstCenter (ratio * radius) (power + 1) time -
          second.exteriorTaylorCoefficient selected secondCenter (ratio * radius) (power + 1) time‖) ≤
        ratio * (∑' power : ℕ, weight ^ (power + 1) *
          ‖first.exteriorTaylorCoefficient selected firstCenter radius (power + 1) time -
            second.exteriorTaylorCoefficient selected secondCenter radius (power + 1) time‖) := by
  have actual := EulerNonuniqueness.General.summable_weighted_tail_dilation
    (fun power : ℕ => first.exteriorTaylorCoefficient selected firstCenter radius (power + 1) time -
      second.exteriorTaylorCoefficient selected secondCenter radius (power + 1) time)
    weightNonnegative ratioNonnegative ratioSmall summable
  simpa only [exteriorTaylorCoefficient_radius_mul, ← smul_sub] using actual

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
