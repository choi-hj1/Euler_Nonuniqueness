import EulerNonuniqueness.Section3.ExponentialStationaryChart
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace EulerNonuniqueness.General

open scoped ContDiff

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

def exponentialStationaryChartPartialHomeomorph (generator : Space →L[ℝ] Space →L[ℝ] Space)
    (base : Space) : PartialHomeomorph Space Space :=
  (exponentialStationaryChart_hasStrictFDerivAt_zero generator base).toPartialHomeomorph
    (exponentialStationaryChart generator base) (f' := ContinuousLinearEquiv.refl ℝ Space)

theorem exponentialStationaryChartPartialHomeomorph_zero_mem_source
    (generator : Space →L[ℝ] Space →L[ℝ] Space) (base : Space) :
    (0 : Space) ∈ (exponentialStationaryChartPartialHomeomorph generator base).source :=
  (exponentialStationaryChart_hasStrictFDerivAt_zero generator base).mem_toPartialHomeomorph_source

theorem exponentialStationaryChartPartialHomeomorph_base_mem_target
    (generator : Space →L[ℝ] Space →L[ℝ] Space) (base : Space) :
    base ∈ (exponentialStationaryChartPartialHomeomorph generator base).target := by
  simpa only [exponentialStationaryChartPartialHomeomorph, HasStrictFDerivAt.toPartialHomeomorph_coe,
    exponentialStationaryChart_zero] using
    (exponentialStationaryChartPartialHomeomorph generator base).map_source
      (exponentialStationaryChartPartialHomeomorph_zero_mem_source generator base)

theorem exponentialStationaryChartPartialHomeomorph_left_inverse
    (generator : Space →L[ℝ] Space →L[ℝ] Space) (base : Space) {increment : Space}
    (inside : increment ∈ (exponentialStationaryChartPartialHomeomorph generator base).source) :
    (exponentialStationaryChartPartialHomeomorph generator base).symm
      (exponentialStationaryChart generator base increment) = increment :=
  (exponentialStationaryChartPartialHomeomorph generator base).left_inv inside

theorem exponentialStationaryChartPartialHomeomorph_inverse_base
    (generator : Space →L[ℝ] Space →L[ℝ] Space) (base : Space) :
    (exponentialStationaryChartPartialHomeomorph generator base).symm base = 0 := by
  simpa only [exponentialStationaryChart_zero] using
    exponentialStationaryChartPartialHomeomorph_left_inverse generator base
      (exponentialStationaryChartPartialHomeomorph_zero_mem_source generator base)

theorem exponentialStationaryChart_inverse_contDiffAt_base
    (generator : Space →L[ℝ] Space →L[ℝ] Space) (base : Space) :
    ContDiffAt ℝ ∞ (exponentialStationaryChartPartialHomeomorph generator base).symm base := by
  apply (exponentialStationaryChartPartialHomeomorph generator base).contDiffAt_symm
    (exponentialStationaryChartPartialHomeomorph_base_mem_target generator base)
    (f₀' := ContinuousLinearEquiv.refl ℝ Space)
  · rw [exponentialStationaryChartPartialHomeomorph_inverse_base]
    exact exponentialStationaryChart_hasFDerivAt_zero generator base
  · rw [exponentialStationaryChartPartialHomeomorph_inverse_base]
    exact (exponentialStationaryChart_analyticAt generator base 0).contDiffAt

theorem exponentialStationaryChart_inverse_analyticAt_base
    (generator : Space →L[ℝ] Space →L[ℝ] Space) (base : Space) :
    AnalyticAt ℝ (exponentialStationaryChartPartialHomeomorph generator base).symm base := by
  have actual := (exponentialStationaryChartPartialHomeomorph generator base).analyticAt_symm'
    (i := ContinuousLinearEquiv.refl ℝ Space)
    (exponentialStationaryChartPartialHomeomorph_zero_mem_source generator base)
    (exponentialStationaryChart_analyticAt generator base 0)
    (exponentialStationaryChart_hasFDerivAt_zero generator base).fderiv
  simpa only [exponentialStationaryChartPartialHomeomorph, HasStrictFDerivAt.toPartialHomeomorph_coe,
    exponentialStationaryChart_zero] using actual

theorem exponentialStationaryChart_inverse_hasStrictFDerivAt_base
    (generator : Space →L[ℝ] Space →L[ℝ] Space) (base : Space) :
    HasStrictFDerivAt (exponentialStationaryChartPartialHomeomorph generator base).symm
      (ContinuousLinearMap.id ℝ Space) base := by
  have actual := (exponentialStationaryChartPartialHomeomorph generator base).hasStrictFDerivAt_symm
    (f' := ContinuousLinearEquiv.refl ℝ Space)
    (exponentialStationaryChartPartialHomeomorph_base_mem_target generator base)
    (by
      rw [exponentialStationaryChartPartialHomeomorph_inverse_base]
      exact exponentialStationaryChart_hasStrictFDerivAt_zero generator base)
  exact actual

end

end EulerNonuniqueness.General
