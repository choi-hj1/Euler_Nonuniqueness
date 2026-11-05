import EulerNonuniqueness.Section8.DisplacementLipschitz
import EulerNonuniqueness.General.BoundedLipschitzODE

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness

theorem exists_displacement_flow_on_Icc {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) {lipschitzBound bound : ℝ≥0}
    (lipschitz : LipschitzWith lipschitzBound kernel) (bounded : ∀ position, ‖kernel position‖ ≤ bound)
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) :
    ∃ path : ℝ → (Plane →ᵇ Plane), path 0 = 0 ∧ ContinuousOn path (Icc 0 horizon) ∧
      (∀ time ∈ Icc 0 horizon, HasDerivWithinAt path
        (displacementVectorField integrable lipschitz.continuous bounded (path time)) (Icc 0 horizon) time) ∧
      ∀ time ∈ Icc 0 horizon, ‖path time‖ ≤ (bound * sourceL1Mass source : ℝ≥0) * time := by
  have fieldBounded (displacement : Plane →ᵇ Plane) :
      ‖displacementVectorField integrable lipschitz.continuous bounded displacement‖ ≤
        (bound * sourceL1Mass source : ℝ≥0) := by
    simpa only [NNReal.coe_mul] using norm_displacementVectorField_le integrable lipschitz.continuous bounded displacement
  simpa only [sub_zero] using exists_solution_Icc_of_bounded_lipschitz
    (lipschitz_displacementVectorField integrable lipschitz bounded) fieldBounded (0 : Plane →ᵇ Plane) nonnegative

theorem hasDerivWithinAt_displacement_trajectory {source : Vorticity} {kernel : Velocity}
    (integrable : Integrable source) (continuous : Continuous kernel) {bound : ℝ≥0}
    (bounded : ∀ position, ‖kernel position‖ ≤ bound) {path : ℝ → (Plane →ᵇ Plane)}
    {region : Set ℝ} {time : ℝ}
    (derivative : HasDerivWithinAt path (displacementVectorField integrable continuous bounded (path time)) region time)
    (label : Plane) :
    HasDerivWithinAt (fun other => label + path other label)
      (∫ sourceLabel, source sourceLabel • kernel ((label + path time label) - (sourceLabel + path time sourceLabel))) region time := by
  have evaluated := (BoundedContinuousFunction.evalCLM ℝ label).hasFDerivAt.comp_hasDerivWithinAt time derivative
  have result := evaluated.const_add label
  convert result using 1
  change (∫ sourceLabel, source sourceLabel • kernel ((label + path time label) - (sourceLabel + path time sourceLabel))) =
    displacementInteraction source kernel (path time) label
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun sourceLabel => by
    dsimp only
    congr 2
    abel

end EulerNonuniqueness
