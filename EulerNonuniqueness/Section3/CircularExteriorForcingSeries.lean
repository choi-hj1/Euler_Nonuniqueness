import EulerNonuniqueness.Section6.ExteriorContourSeries
import EulerNonuniqueness.Section3.DiskForcingPhaseRotation

namespace EulerNonuniqueness.Paper

noncomputable section

open MeasureTheory
open scoped ENNReal
open EulerNonuniqueness.Section6

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance circularExteriorSeriesC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem rotatedExteriorMode_eq_diskForcingTerm (power : ℕ) (frequency time : ℝ) (amplitude : ℝ → ℂ) :
    rotatedExteriorMode (Circle.exp (frequency * time / 2)) power (amplitude time) =
      diskForcingTerm power frequency amplitude time := by
  unfold rotatedExteriorMode diskForcingTerm
  rw [diskForcingPhase_eq_rotation_power, mul_comm]

theorem circularExteriorForcing_eq_diskForcingSum {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    {center : ℂ} {radius distance : ℝ} (source : SpatialContourField center radius)
    (fieldIdentity : source.field = biotSavart vorticity) (frequency time : ℝ)
    (radiusPositive : 0 < radius) (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (small : 2 * radius / distance < 1) :
    source.rotatedCompose standardCircleBanach (Circle.exp (frequency * time / 2)) radiusPositive
      (standardCircleBanach_norm_bound.trans (by norm_num)) =
      ∑' power, diskForcingTerm power frequency
        (fun _ => exteriorVorticityCoefficient vorticity center radius power) time := by
  rw [exterior_contour_series_eq integrable membership source fieldIdentity
    (Circle.exp (frequency * time / 2)) radiusPositive positive separated small]
  apply tsum_congr
  intro power
  exact rotatedExteriorMode_eq_diskForcingTerm power frequency time
    (fun _ => exteriorVorticityCoefficient vorticity center radius power)

end

end EulerNonuniqueness.Paper
