import EulerNonuniqueness.Section8.RegularizedApproximation
import EulerNonuniqueness.Section8.RegularizedVelocityConvergence

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem tendstoUniformly_regularizedApproximation_velocity_defect {source : Vorticity}
    (integrable : Integrable source) {horizon : ℝ} (nonnegative : 0 ≤ horizon)
    (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume) :
    TendstoUniformly (fun index (point : Icc 0 horizon × Plane) =>
      regularizedBiotSavart (regularizationScale index)
          (regularizedApproximation integrable nonnegative index point.1) point.2 -
        biotSavart (regularizedApproximation integrable nonnegative index point.1) point.2)
      (fun _ => 0) atTop := by
  apply tendstoUniformly_regularizedBiotSavart_sub regularizationScale_positive tendsto_regularizationScale
    (vorticity := fun index (time : Icc 0 horizon) => regularizedApproximation integrable nonnegative index time)
    (fun index time => (regularizedApproximationFlow integrable nonnegative index).integrable_vorticity nonnegative time.property)
    (fun index time => (regularizedApproximationFlow integrable nonnegative index).memLp_vorticity nonnegative time.property membership)
    (oneBound := ∫ label, ‖source label‖)
    (fourBound := (eLpNorm source (ENNReal.ofReal (4 : ℝ)) volume).toReal)
  · intro index time
    exact ((regularizedApproximationFlow integrable nonnegative index).integral_norm_vorticity nonnegative time.property).le
  · intro index time
    exact (congrArg ENNReal.toReal
      ((regularizedApproximationFlow integrable nonnegative index).eLpNorm_vorticity nonnegative time.property
        (ENNReal.ofReal (4 : ℝ)))).le

end EulerNonuniqueness
