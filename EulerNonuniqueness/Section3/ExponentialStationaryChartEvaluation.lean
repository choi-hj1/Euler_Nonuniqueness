import EulerNonuniqueness.Section3.ExponentialStationaryChart
import EulerNonuniqueness.General.LinearExponentialCurve

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem exponentialStationaryChart_evaluation
    (generator : Space →L[ℝ] Space →L[ℝ] Space) (base increment : Space)
    (evaluation : Space →L[ℝ] ℂ) (coefficient : ℂ)
    (intertwines : ∀ value, evaluation (generator increment value) = coefficient * evaluation value) :
    evaluation (exponentialStationaryChart generator base increment) =
      Complex.exp coefficient * (evaluation base + evaluation increment - coefficient * evaluation base) := by
  have actual := linearExponentialCurve_evaluation (generator increment)
    (base + increment - generator increment base) evaluation coefficient intertwines 1
  simpa only [linearExponentialCurve, one_smul, Complex.ofReal_one, one_mul,
    exponentialStationaryChart, map_sub, map_add, intertwines] using actual

theorem exponentialStationaryChart_neutral_value
    (generator : Space →L[ℝ] Space →L[ℝ] Space) (base increment : Space)
    (neutral : generator increment base = increment) :
    exponentialStationaryChart generator base increment =
      (NormedSpace.exp ℝ (generator increment)) base := by
  simp only [exponentialStationaryChart, neutral, add_sub_cancel_right]

end

end EulerNonuniqueness.General
