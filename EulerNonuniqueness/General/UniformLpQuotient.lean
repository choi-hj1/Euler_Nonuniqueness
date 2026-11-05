import Mathlib

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureTheory

theorem eventually_uniform_eLpNorm_sub_lt_of_tendstoUniformly_toLp
    {Domain Value Parameter : Type*} [MeasurableSpace Domain]
    [NormedAddCommGroup Value] {measure : Measure Domain} {exponent : ℝ≥0∞}
    [Fact (1 ≤ exponent)] {sequence : ℕ → Parameter → Domain → Value}
    {limit : Parameter → Domain → Value}
    (members : ∀ index parameter, MemLp (sequence index parameter) exponent measure)
    (limitMembers : ∀ parameter, MemLp (limit parameter) exponent measure)
    (converges : TendstoUniformly
      (fun index parameter => (members index parameter).toLp (sequence index parameter))
      (fun parameter => (limitMembers parameter).toLp (limit parameter)) atTop)
    {tolerance : ℝ} (positive : 0 < tolerance) :
    ∀ᶠ index in atTop, ∀ parameter,
      eLpNorm (sequence index parameter - limit parameter) exponent measure < ENNReal.ofReal tolerance := by
  filter_upwards [Metric.tendstoUniformly_iff.mp converges tolerance positive] with index bound
  intro parameter
  apply (ENNReal.lt_ofReal_iff_toReal_lt
    ((members index parameter).sub (limitMembers parameter)).eLpNorm_lt_top.ne).mpr
  have normEquality :
      dist ((limitMembers parameter).toLp (limit parameter))
        ((members index parameter).toLp (sequence index parameter)) =
      (eLpNorm (sequence index parameter - limit parameter) exponent measure).toReal := by
    rw [dist_comm, dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
  rw [← normEquality]
  exact bound parameter

end MeasureTheory
