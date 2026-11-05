import EulerNonuniqueness.Section6.PhysicalVorticityStrainMultipole
import EulerNonuniqueness.Section6.PaperQuadrupoleStaticMoments

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.integrable_patchDensity_kernelStrain
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (patch : Fin 4) {location : ℂ} {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ source ∈ motion.domain time index patch, distance ≤ ‖location - source‖) :
    Integrable (fun source => patchDensity scales motion time index patch source •
      Section6.biotSavartKernelStrain location source) := by
  have properties := evolution.2.2.2.1 time inside index patch
  have integrable := Section6.integrableOn_biotSavartKernelStrain_of_separation properties.1.measurableSet
    properties.2.1.measure_lt_top positive separated
  have identity : (fun source => patchDensity scales motion time index patch source •
      Section6.biotSavartKernelStrain location source) =
      fun source => (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) •
        (motion.domain time index patch).indicator (Section6.biotSavartKernelStrain location) source := by
    funext source
    by_cases member : source ∈ motion.domain time index patch <;> simp [patchDensity, member]
  rw [identity]
  exact ((integrable_indicator_iff properties.1.measurableSet).mpr integrable).smul _

theorem FinitePatchEvolution.quadrupoleComplexStrain_sum
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) {location : ℂ} {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ patch, ∀ source ∈ motion.domain time index patch, distance ≤ ‖location - source‖) :
    Section6.vorticityComplexStrain (quadrupoleDensity scales motion time index) location =
      ∑ patch : Fin 4, (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) •
        ∫ source in motion.domain time index patch, Section6.biotSavartKernelStrain location source := by
  simp only [Section6.vorticityComplexStrain, quadrupoleDensity, Finset.sum_smul]
  rw [integral_finset_sum _ (fun patch _ => evolution.integrable_patchDensity_kernelStrain
    inside index patch positive (separated patch))]
  exact Finset.sum_congr rfl (fun patch _ => evolution.integral_patchDensity_smul inside index patch _)

theorem FinitePatchEvolution.quadrupole_biotSavart_hasFDerivAt_complexStrain
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) {location : ℂ} {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ patch, ∀ source ∈ motion.domain time index patch, distance ≤ ‖location - source‖) :
    HasFDerivAt (biotSavart (quadrupoleDensity scales motion time index))
      (Section6.vorticityComplexStrain (quadrupoleDensity scales motion time index) location •
        (Complex.conjCLE : ℂ →L[ℝ] ℂ)) location := by
  have derivative := HasFDerivAt.sum (u := Finset.univ) (fun patch (_ : patch ∈ Finset.univ) =>
    Section6.indicator_biotSavart_hasFDerivAt_of_separation
      (evolution.2.2.2.1 time inside index patch).1.measurableSet
      (evolution.2.2.2.1 time inside index patch).2.1.measure_lt_top
      (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) positive (separated patch))
  have identity : biotSavart (quadrupoleDensity scales motion time index) =
      fun position => ∑ patch : Fin 4, biotSavart (patchDensity scales motion time index patch) position :=
    funext (evolution.quadrupole_biotSavart_eq_sum_patch inside index)
  have operatorIdentity :
      (∑ patch : Fin 4, (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) •
        ∫ source in motion.domain time index patch, Section6.biotSavartKernelStrain location source) •
          (Complex.conjCLE : ℂ →L[ℝ] ℂ) =
      ∑ patch : Fin 4, ((patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) •
        ∫ source in motion.domain time index patch, Section6.biotSavartKernelStrain location source) •
          (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
    ext increment
    simp [ContinuousLinearMap.smul_apply, Finset.sum_mul]
  rw [identity, evolution.quadrupoleComplexStrain_sum inside index positive separated, operatorIdentity]
  exact derivative

end EulerNonuniqueness.Paper
