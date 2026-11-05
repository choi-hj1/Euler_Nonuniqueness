import EulerNonuniqueness.General.QuadraticResonanceEvaluation

namespace EulerNonuniqueness.General

noncomputable section

open MeasureTheory

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem quadraticHomologicalSolution_apply_integral
    (group : ℝ → Space →L[ℝ] Space) (period : ℝ) (bilinear : BilinearEnd Space)
    (continuousConjugate : Continuous (fun time => quadraticConjugate group time bilinear))
    (first second : Space) :
    quadraticHomologicalSolution group period bilinear first second =
      (1 / period : ℝ) • ∫ time in (0 : ℝ)..period,
        time • group (-time) (bilinear (group time first) (group time second)) := by
  let evaluate : BilinearEnd Space →L[ℝ] Space :=
    (ContinuousLinearMap.apply ℝ Space second).comp
      (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) first)
  have integral := ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
    (E := BilinearEnd Space) (F := Space) (μ := volume) evaluate
    ((continuous_id.smul continuousConjugate).intervalIntegrable 0 period)
  change (∫ time in (0 : ℝ)..period,
    evaluate (time • quadraticConjugate group time bilinear)) =
      evaluate (∫ time in (0 : ℝ)..period, time • quadraticConjugate group time bilinear) at integral
  have evaluated (time : ℝ) : evaluate (time • quadraticConjugate group time bilinear) =
      time • group (-time) (bilinear (group time first) (group time second)) := rfl
  simp only [evaluated] at integral
  rw [integral]
  exact evaluate.map_smul _ _

theorem quadraticHomologicalSolution_diagonal_zero_of_fixed
    (group : ℝ → Space →L[ℝ] Space) (period : ℝ) (bilinear : BilinearEnd Space)
    (continuousConjugate : Continuous (fun time => quadraticConjugate group time bilinear))
    (neutral : Space) (fixed : ∀ time, group time neutral = neutral)
    (diagonalZero : bilinear neutral neutral = 0) :
    quadraticHomologicalSolution group period bilinear neutral neutral = 0 := by
  rw [quadraticHomologicalSolution_apply_integral group period bilinear continuousConjugate]
  simp only [fixed, diagonalZero, map_zero, smul_zero, intervalIntegral.integral_zero]

end

end EulerNonuniqueness.General
