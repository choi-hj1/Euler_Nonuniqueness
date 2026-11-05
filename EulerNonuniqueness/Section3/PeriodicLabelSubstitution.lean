import EulerNonuniqueness.Section3.HolderLabelComposition
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.PeriodicC1LabelMap

theorem image_Ioc_of_slope_pos (labels : PeriodicC1LabelMap)
    (positive : ∀ label, 0 < labels.slope label) {lower upper : ℝ} (ordered : lower ≤ upper) :
    labels.map '' Ioc lower upper = Ioc (labels.map lower) (labels.map upper) := by
  have monotone := strictMono_of_hasDerivAt_pos labels.hasDerivAt positive
  apply subset_antisymm monotone.image_Ioc_subset
  intro value member
  obtain ⟨label, labelInside, valueIdentity⟩ := intermediate_value_Icc ordered labels.continuous.continuousOn
    ⟨member.1.le, member.2⟩
  refine ⟨label, ⟨?_, labelInside.2⟩, valueIdentity⟩
  exact (monotone.lt_iff_lt).mp (by simpa only [valueIdentity] using member.1)

theorem intervalIntegral_substitution (labels : PeriodicC1LabelMap)
    (positive : ∀ label, 0 < labels.slope label) {lower upper : ℝ} (ordered : lower ≤ upper)
    (function : ℝ → ℂ)
    (integrable : IntervalIntegrable function volume (labels.map lower) (labels.map upper)) :
    IntervalIntegrable (fun label => labels.slope label • function (labels.map label)) volume lower upper ∧
      (∫ label in lower..upper, labels.slope label • function (labels.map label)) =
        ∫ label in (labels.map lower)..(labels.map upper), function label := by
  have monotone := strictMono_of_hasDerivAt_pos labels.hasDerivAt positive
  have image := labels.image_Ioc_of_slope_pos positive ordered
  have imageIntegrable : IntegrableOn function (labels.map '' Ioc lower upper) := by
    rw [image]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (monotone.monotone ordered)).mp integrable
  have pullback := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc
    (fun label _ => (labels.hasDerivAt label).hasDerivWithinAt) monotone.injective.injOn function).mp imageIntegrable
  have substitution := integral_image_eq_integral_abs_deriv_smul (s := Ioc lower upper) measurableSet_Ioc
    (fun label _ => (labels.hasDerivAt label).hasDerivWithinAt) monotone.injective.injOn function
  simp only [abs_of_pos (positive _)] at pullback substitution
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ordered).mpr pullback, ?_⟩
  rw [intervalIntegral.integral_of_le ordered,
    intervalIntegral.integral_of_le (monotone.monotone ordered), ← image]
  exact substitution.symm

end EulerNonuniqueness.Paper.PeriodicC1LabelMap
