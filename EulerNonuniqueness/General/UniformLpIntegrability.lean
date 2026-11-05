import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem unifIntegrable_of_uniform_higherLp {Domain Value Index : Type*}
    [MeasurableSpace Domain] [NormedAddCommGroup Value] {measure : Measure Domain}
    {sequence : Index → Domain → Value} {exponent higherExponent : ℝ≥0∞}
    (exponentPositive : 0 < exponent) (strict : exponent < higherExponent)
    (higherFinite : higherExponent ≠ ∞)
    (measurable : ∀ index, AEStronglyMeasurable (sequence index) measure)
    {bound : ℝ} (boundNonnegative : 0 ≤ bound)
    (normBound : ∀ index, eLpNorm (sequence index) higherExponent measure ≤ ENNReal.ofReal bound) :
    UnifIntegrable sequence exponent measure := by
  have exponentFinite : exponent ≠ ∞ := (strict.trans_le le_top).ne
  have exponentRealPositive : 0 < exponent.toReal :=
    ENNReal.toReal_pos exponentPositive.ne' exponentFinite
  have higherRealPositive : 0 < higherExponent.toReal :=
    ENNReal.toReal_pos (exponentPositive.trans strict).ne' higherFinite
  have realStrict : exponent.toReal < higherExponent.toReal :=
    (ENNReal.toReal_lt_toReal exponentFinite higherFinite).mpr strict
  have powerPositive : 0 < 1 / exponent.toReal - 1 / higherExponent.toReal :=
    sub_pos.mpr ((one_div_lt_one_div higherRealPositive exponentRealPositive).mpr realStrict)
  intro epsilon epsilonPositive
  let delta := (epsilon / (bound + 1)) ^ (1 / (1 / exponent.toReal - 1 / higherExponent.toReal))
  have deltaPositive : 0 < delta := Real.rpow_pos_of_pos (by positivity) _
  have deltaPower : delta ^ (1 / exponent.toReal - 1 / higherExponent.toReal) =
      epsilon / (bound + 1) := by
    dsimp only [delta]
    rw [one_div, Real.rpow_inv_rpow (by positivity) powerPositive.ne']
  refine ⟨delta, deltaPositive, fun index subset subsetMeasurable measureSmall => ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict subsetMeasurable]
  calc
    _ ≤ eLpNorm (sequence index) higherExponent (measure.restrict subset) *
        (measure.restrict subset) univ ^ (1 / exponent.toReal - 1 / higherExponent.toReal) :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ strict.le (measurable index).restrict
    _ ≤ ENNReal.ofReal bound *
        ENNReal.ofReal delta ^ (1 / exponent.toReal - 1 / higherExponent.toReal) := by
      gcongr
      · exact (eLpNorm_restrict_le _ _ _ _).trans (normBound index)
      · simpa only [Measure.restrict_apply_univ] using measureSmall
    _ = ENNReal.ofReal (bound * (epsilon / (bound + 1))) := by
      rw [ENNReal.ofReal_rpow_of_nonneg deltaPositive.le powerPositive.le, deltaPower,
        ← ENNReal.ofReal_mul boundNonnegative]
    _ ≤ ENNReal.ofReal epsilon := by
      apply ENNReal.ofReal_le_ofReal
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < bound + 1)).mpr
      nlinarith

end EulerNonuniqueness
