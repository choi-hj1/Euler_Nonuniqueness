import EulerNonuniqueness.Section3.FiniteLiteralPatchFlow
import EulerNonuniqueness.Section3.AffinePatchReynolds
import EulerNonuniqueness.Section3.AffinePatchAdvection
import Mathlib.Analysis.Calculus.Deriv.Prod

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance literalPatchMomentsHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance literalPatchMomentsC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem vorticity_memLp (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (exponent : ℝ≥0∞) :
    MemLp (flow.vorticity time) exponent volume := by
  exact memLp_finset_sum Finset.univ fun index _ =>
    (configuration.literalIndicator_memLp (flow.shape time)
      (fun index => (flow.nearby time index).trans_le (min_le_left _ _)) index exponent).const_mul _

theorem vorticity_integrable (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) :
    Integrable (flow.vorticity time) := memLp_one_iff_integrable.mp (flow.vorticity_memLp time 1)

theorem shape_component_hasDerivAt (flow : FiniteLiteralPatchFlow configuration) {time : ℝ}
    (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    HasDerivAt (fun parameter => flow.shape parameter index) (configuration.vectorField (flow.shape time) index) time := by
  exact (hasDerivAt_pi (𝕜 := ℝ) (E' := fun _ : Fin count => PeriodicC1HolderHalf)
    (φ := flow.shape) (φ' := configuration.vectorField (flow.shape time)) (x := time)).mp
      (flow.equation time inside) index

theorem domain_integral_hasDerivAt (flow : FiniteLiteralPatchFlow configuration) {time : ℝ}
    (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count)
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ position, HasFDerivAt function (derivative position) position) :
    HasDerivAt (fun parameter => ∫ position in flow.domain parameter index, function position)
      (∫ position in flow.domain time index, derivative position (biotSavart (flow.vorticity time) position)) time := by
  let radius := min (time + flow.duration) (flow.duration - time)
  have radius_positive : 0 < radius := lt_min (by linarith [inside.1]) (by linarith [inside.2])
  have ball_inside : ∀ parameter ∈ Metric.ball time radius, parameter ∈ Ioo (-flow.duration) flow.duration := by
    intro parameter close
    have distance : |parameter - time| < radius := by simpa only [Metric.mem_ball, Real.dist_eq] using close
    have lower := min_le_left (time + flow.duration) (flow.duration - time)
    have upper := min_le_right (time + flow.duration) (flow.duration - time)
    dsimp only [radius] at distance
    constructor <;> linarith [(abs_lt.mp distance).1, (abs_lt.mp distance).2]
  have reynolds := affinePatchDomain_hasDerivAt_integral (configuration.center index) (configuration.radius_pos index)
    (fun parameter => flow.shape parameter index)
    (fun parameter => configuration.vectorField (flow.shape parameter) index)
    ((continuous_apply index).comp flow.continuous)
    ((continuous_apply index).comp flow.velocity_continuous)
    (fun parameter => (flow.nearby parameter index).trans_le (min_le_left _ _))
    time radius radius_positive
    (fun parameter close => flow.shape_component_hasDerivAt (ball_inside parameter close) index)
    function derivative function_continuous derivative_continuous function_derivative
  have flux_identity := integral_affinePatchDomain_biotSavart_advection (configuration.center index)
    (configuration.radius_pos index) (flow.shape time index)
    ((flow.nearby time index).trans_le (min_le_left _ _)) function derivative
    function_continuous derivative_continuous function_derivative
    (flow.vorticity_integrable time) (flow.vorticity_memLp time (ENNReal.ofReal (4 : ℝ)))
  have coefficient_identity :
      (∫ position in flow.domain time index, derivative position (biotSavart (flow.vorticity time) position)) =
      ∫ label in (-Real.pi)..Real.pi,
        function (configuration.center index + configuration.radius index • (flow.shape time index).val.1 label) *
          contourAreaPair (configuration.radius index • (configuration.vectorField (flow.shape time) index).val.1 label)
            (configuration.radius index • (flow.shape time index).val.2.val.1 label) := by
    dsimp only [domain, FiniteContourConfiguration.literalDomain]
    rw [flux_identity]
    apply intervalIntegral.integral_congr
    intro label _
    dsimp only
    congr 2
    exact flow.velocity_eq time index label
  rw [coefficient_identity]
  exact reynolds

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
