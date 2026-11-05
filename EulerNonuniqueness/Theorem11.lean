import EulerNonuniqueness.Section7.ActualApproximationExistence
import EulerNonuniqueness.Section8.Assembly

/-! Theorem 1.1, from the actual finite cascades and the global Euler assembly. -/

namespace EulerNonuniqueness

theorem theorem11 : Theorem11 := by
  obtain ⟨data⟩ := Paper.exists_actual_approximation_data
  exact nonuniqueness_of_approximation_data data

end EulerNonuniqueness
