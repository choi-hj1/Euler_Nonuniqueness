import EulerNonuniqueness.Section3.FinitePatchSupport

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem support_patchVorticity_subset_of_domain_subset {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) {region : Set Plane}
    (domainSubset : ∀ index patch, motion.domain time index patch ⊆ region) :
    Function.support (patchVorticity scales motion time) ⊆ region := by
  intro position nonzero
  by_contra outside
  have densityZero (index : Fin count) (patch : Fin 4) : patchDensity scales motion time index patch position = 0 :=
    indicator_of_not_mem (fun inside => outside (domainSubset index patch inside)) _
  exact nonzero (by simp only [patchVorticity, quadrupoleDensity, densityZero, Finset.sum_const_zero])

end EulerNonuniqueness.Paper
