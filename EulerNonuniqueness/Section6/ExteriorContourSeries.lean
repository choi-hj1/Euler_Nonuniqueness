import EulerNonuniqueness.Section6.ExteriorBiotSavartSeries
import EulerNonuniqueness.Section3.SpatialContourComposition
import EulerNonuniqueness.Section3.DiskForcingSeriesEquation
import EulerNonuniqueness.Section3.ContourLocalEvolution

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

local instance exteriorSeriesC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

def rotatedExteriorMode (phase : Circle) (power : ℕ) (coefficient : ℂ) : PeriodicC1HolderHalf :=
  ((phase : ℂ)⁻¹ ^ (power + 2) * coefficient) • c1Conjugate (diskCircleMode (power + 1))

theorem rotatedExteriorMode_norm_bound (phase : Circle) (power : ℕ) (coefficient : ℂ) :
    ‖rotatedExteriorMode phase power coefficient‖ ≤ 8 * ((2 : ℝ) ^ (power + 1) * ‖coefficient‖) := by
  unfold rotatedExteriorMode
  rw [norm_smul, norm_mul, norm_pow, norm_inv, Circle.norm_coe, inv_one, one_pow, one_mul]
  have estimate := mul_le_mul_of_nonneg_left
    (diskCircleMode_geometric_norm_bound power) (norm_nonneg coefficient)
  convert estimate using 1 <;> ring

theorem rotatedExteriorMode_summable (phase : Circle) (coefficient : ℕ → ℂ)
    (weighted : Summable (fun power => (2 : ℝ) ^ (power + 1) * ‖coefficient power‖)) :
    Summable (fun power => rotatedExteriorMode phase power (coefficient power)) :=
  Summable.of_norm_bounded _ (weighted.mul_left 8) (fun power => rotatedExteriorMode_norm_bound phase power _)

theorem exterior_contour_series_eq {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    {center : ℂ} {radius distance : ℝ} (source : SpatialContourField center radius)
    (fieldIdentity : source.field = biotSavart vorticity) (phase : Circle)
    (radiusPositive : 0 < radius) (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (small : 2 * radius / distance < 1) :
    source.rotatedCompose standardCircleBanach phase radiusPositive
      (standardCircleBanach_norm_bound.trans (by norm_num)) =
      ∑' power, rotatedExteriorMode phase power (exteriorVorticityCoefficient vorticity center radius power) := by
  have weighted := summable_weighted_exteriorVorticityCoefficient integrable center radiusPositive.le positive separated small
  have summableModes := rotatedExteriorMode_summable phase _ weighted
  have ratioSmall : radius / distance < 1 := by
    rw [mul_div_assoc] at small
    have nonnegative := div_nonneg radiusPositive.le positive.le
    linarith
  have conjugatePhase : star (phase : ℂ) = (phase : ℂ)⁻¹ := by
    exact (Circle.coe_inv_eq_conj phase).symm
  apply PeriodicC1HolderHalf.ext_value
  intro label
  have modeSeries := (contourLabelEvaluation label).hasSum summableModes.hasSum
  have physicalSeries := (exterior_biotSavart_series_hasSum integrable membership center
    ((phase : ℂ) * standardCircle label) radiusPositive positive separated
    (by simpa only [norm_mul, Circle.norm_coe, standardCircle_norm, mul_one, one_mul] using ratioSmall)).mul_left
      (phase : ℂ)⁻¹
  have sameTerms : (fun power : ℕ => (contourLabelEvaluation label)
      (rotatedExteriorMode phase power (exteriorVorticityCoefficient vorticity center radius power))) =
      fun power : ℕ => (phase : ℂ)⁻¹ *
        (exteriorVorticityCoefficient vorticity center radius power *
          (star ((phase : ℂ) * standardCircle label)) ^ (power + 1)) := by
    funext power
    change (((phase : ℂ)⁻¹ ^ (power + 2) * exteriorVorticityCoefficient vorticity center radius power) •
      c1Conjugate (diskCircleMode (power + 1))).val.1 label = _
    rw [complexC1Holder_smul_value, c1Conjugate_value, diskCircleMode_value]
    simp only [star_mul, star_pow, conjugatePhase, pow_add, pow_succ]
    ring
  rw [sameTerms] at modeSeries
  have identity := physicalSeries.unique modeSeries
  rw [SpatialContourField.rotatedCompose_value, fieldIdentity]
  change radius⁻¹ • ((phase : ℂ)⁻¹ *
    (biotSavart vorticity (center + radius • ((phase : ℂ) * standardCircle label)) - biotSavart vorticity center)) = _
  rw [Complex.real_smul, Complex.real_smul, Complex.ofReal_inv]
  convert identity using 1 <;> ring

end EulerNonuniqueness.Paper
