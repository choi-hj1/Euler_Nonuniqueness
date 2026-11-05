import EulerNonuniqueness.General.PeriodicQuadraticHomological

namespace EulerNonuniqueness.General

noncomputable section

open MeasureTheory

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem quadraticResonance_apply_integral
    (group : ℝ → Space →L[ℝ] Space) (period : ℝ) (bilinear : BilinearEnd Space)
    (continuousConjugate : Continuous (fun time => quadraticConjugate group time bilinear))
    (first second : Space) :
    quadraticResonance group period bilinear first second =
      (1 / period : ℝ) • ∫ time in (0 : ℝ)..period,
        group (-time) (bilinear (group time first) (group time second)) := by
  let evaluate : BilinearEnd Space →L[ℝ] Space :=
    (ContinuousLinearMap.apply ℝ Space second).comp
      (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) first)
  have commutation :
      (∫ time in (0 : ℝ)..period, group (-time) (bilinear (group time first) (group time second))) =
      evaluate (∫ time in (0 : ℝ)..period, quadraticConjugate group time bilinear) :=
    by
      have raw := ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
        (E := BilinearEnd Space) (F := Space) (μ := volume) evaluate
        (continuousConjugate.intervalIntegrable 0 period)
      exact raw
  rw [commutation]
  change evaluate ((1 / period : ℝ) • ∫ time in (0 : ℝ)..period, quadraticConjugate group time bilinear) = _
  exact evaluate.map_smul _ _

end

end EulerNonuniqueness.General
