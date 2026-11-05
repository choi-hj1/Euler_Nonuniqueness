import EulerNonuniqueness.Section6.ExteriorContourSeries
import EulerNonuniqueness.Section3.ExteriorCoefficientWeights
import EulerNonuniqueness.Section3.C1PowerGeometricBound

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

local instance generalExteriorSeriesC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

def rotatedExteriorPower (phase : Circle) (data : PeriodicC1HolderHalf)
    (power : ℕ) (coefficient : ℂ) : PeriodicC1HolderHalf :=
  ((phase : ℂ)⁻¹ ^ (power + 2) * coefficient) • c1Conjugate (c1NaturalPower data (power + 1))

theorem rotatedExteriorPower_norm_bound (phase : Circle) (data : PeriodicC1HolderHalf)
    (bound : ‖data‖ ≤ 3) (power : ℕ) (coefficient : ℂ) :
    ‖rotatedExteriorPower phase data power coefficient‖ ≤
      (24 : ℝ) ^ (power + 1) * ‖coefficient‖ := by
  unfold rotatedExteriorPower
  rw [norm_smul, norm_mul, norm_pow, norm_inv, Circle.norm_coe, inv_one, one_pow, one_mul]
  have estimate := mul_le_mul_of_nonneg_left
    ((c1Conjugate_norm_bound _).trans (c1NaturalPower_norm_bound_twentyFour data bound (power + 1)))
    (norm_nonneg coefficient)
  simpa only [mul_comm] using estimate

theorem rotatedExteriorPower_summable (phase : Circle) (data : PeriodicC1HolderHalf)
    (bound : ‖data‖ ≤ 3) (coefficient : ℕ → ℂ)
    (weighted : Summable (fun power => (24 : ℝ) ^ (power + 1) * ‖coefficient power‖)) :
    Summable (fun power => rotatedExteriorPower phase data power (coefficient power)) :=
  Summable.of_norm_bounded _ weighted (fun power => rotatedExteriorPower_norm_bound phase data bound power _)

theorem exterior_general_contour_series_eq {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    {center : ℂ} {radius distance : ℝ} (source : SpatialContourField center radius)
    (fieldIdentity : source.field = biotSavart vorticity) (phase : Circle)
    (data : PeriodicC1HolderHalf) (bound : ‖data‖ ≤ 3)
    (radiusPositive : 0 < radius) (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (small : 24 * radius / distance < 1) :
    source.rotatedCompose data phase radiusPositive bound =
      ∑' power, rotatedExteriorPower phase data power
        (exteriorVorticityCoefficient vorticity center radius power) := by
  have weighted := summable_exteriorVorticityCoefficient_weight integrable center
    radiusPositive.le positive (by norm_num : (0 : ℝ) ≤ 24) separated small
  have summablePowers := rotatedExteriorPower_summable phase data bound _ weighted
  have radiusBound : 24 * radius < distance := (div_lt_one positive).mp small
  have conjugatePhase : star (phase : ℂ) = (phase : ℂ)⁻¹ := (Circle.coe_inv_eq_conj phase).symm
  apply PeriodicC1HolderHalf.ext_value
  intro label
  have pointBound : ‖data.val.1 label‖ ≤ 3 := (PeriodicC1HolderHalf.value_bound data label).trans bound
  have pointSmall : radius * ‖(phase : ℂ) * data.val.1 label‖ / distance < 1 := by
    rw [norm_mul, Circle.norm_coe, one_mul]
    apply (div_lt_one positive).mpr
    have scaled := mul_le_mul_of_nonneg_left pointBound radiusPositive.le
    nlinarith
  have powerSeries := (contourLabelEvaluation label).hasSum summablePowers.hasSum
  have physicalSeries := (exterior_biotSavart_series_hasSum integrable membership center
    ((phase : ℂ) * data.val.1 label) radiusPositive positive separated pointSmall).mul_left (phase : ℂ)⁻¹
  have sameTerms : (fun power : ℕ => contourLabelEvaluation label
      (rotatedExteriorPower phase data power (exteriorVorticityCoefficient vorticity center radius power))) =
      fun power : ℕ => (phase : ℂ)⁻¹ * (exteriorVorticityCoefficient vorticity center radius power *
        (star ((phase : ℂ) * data.val.1 label)) ^ (power + 1)) := by
    funext power
    change (((phase : ℂ)⁻¹ ^ (power + 2) * exteriorVorticityCoefficient vorticity center radius power) •
      c1Conjugate (c1NaturalPower data (power + 1))).val.1 label = _
    rw [complexC1Holder_smul_value, c1Conjugate_value, c1NaturalPower_value]
    simp only [star_mul, star_pow, conjugatePhase, pow_add, pow_succ]
    ring
  rw [sameTerms] at powerSeries
  have identity := physicalSeries.unique powerSeries
  rw [SpatialContourField.rotatedCompose_value, fieldIdentity]
  change radius⁻¹ • ((phase : ℂ)⁻¹ *
    (biotSavart vorticity (center + radius • ((phase : ℂ) * data.val.1 label)) - biotSavart vorticity center)) = _
  rw [Complex.real_smul, Complex.real_smul, Complex.ofReal_inv]
  convert identity using 1 <;> ring

end EulerNonuniqueness.Paper
