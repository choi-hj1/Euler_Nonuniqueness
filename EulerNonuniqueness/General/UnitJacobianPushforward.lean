import Mathlib.MeasureTheory.Function.Jacobian

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace EulerNonuniqueness

theorem map_eq_restrict_range_of_unit_jacobian {Space : Type*}
    [NormedAddCommGroup Space] [NormedSpace ℝ Space] [FiniteDimensional ℝ Space]
    [MeasurableSpace Space] [BorelSpace Space] (measure : Measure Space) [IsAddHaarMeasure measure]
    {function : Space → Space} {derivative : Space → Space →L[ℝ] Space}
    (differentiable : ∀ point, HasFDerivAt function (derivative point) point)
    (injective : Function.Injective function)
    (unitJacobian : ∀ point, LinearMap.det (derivative point).toLinearMap = 1) :
    Measure.map function measure = measure.restrict (range function) := by
  have continuous : Continuous function := continuous_iff_continuousAt.mpr
    (fun point => (differentiable point).continuousAt)
  have changeOfVariables := MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar measure
    (s := univ) (f := function) (f' := derivative) MeasurableSet.univ
    (fun point _ => (differentiable point).hasFDerivWithinAt) injective.injOn continuous.measurable
  simp only [ContinuousLinearMap.det, unitJacobian, abs_one, ENNReal.ofReal_one,
    Measure.restrict_univ, image_univ] at changeOfVariables
  change Measure.map function (measure.withDensity 1) = _ at changeOfVariables
  rwa [withDensity_one] at changeOfVariables

end EulerNonuniqueness
