import EulerNonuniqueness.Section3.MovingSmoothMomentRegularity
import EulerNonuniqueness.General.LocalC1Extension
import EulerNonuniqueness.Section6.SmoothConjugateInversePower
import EulerNonuniqueness.Section6.MovingExteriorTaylorCoefficient

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem MovingMaterialPatch.domain_conjugate_inverse_power_contDiffAt_of_local_center
    (path : MovingMaterialPatch) {time distance : ℝ} (inside : time ∈ Ioo path.initialTime path.finalTime)
    (distancePositive : 0 < distance) (center : ℝ → ℂ) (centerSmooth : ContDiffAt ℝ 1 center time)
    (separatedNear : ∀ᶠ parameter in 𝓝 time, ∀ position ∈ path.domain parameter,
      distance ≤ ‖center parameter - position‖) (power : ℕ) :
    ContDiffAt ℝ 1 (fun parameter => ∫ position in path.domain parameter,
      (star (center parameter - position))⁻¹ ^ (power + 1)) time := by
  obtain ⟨extension, velocity, extensionContinuous, velocityContinuous, equation, agreement⟩ :=
    General.exists_global_c1_extension_of_contDiffAt centerSmooth
  have extensionSmooth : ContDiff ℝ 1 extension := by
    apply contDiff_iff_contDiffAt.mpr
    intro parameter
    apply contDiffAt_one_iff.mpr
    refine ⟨fun current => (1 : ℝ →L[ℝ] ℝ).smulRight (velocity current), univ, Filter.univ_mem, ?_, ?_⟩
    · exact (((ContinuousLinearMap.smulRightL ℝ ℝ ℂ) 1).continuous.comp velocityContinuous).continuousOn
    · intro current _
      exact (equation current).hasFDerivAt
  let function : ℝ × ℂ → ℂ := fun point =>
    Section6.smoothConjugateInversePower distance (power + 1) (extension point.1 - point.2)
  have functionSmooth : ContDiff ℝ 1 function :=
    ((Section6.smoothConjugateInversePower_contDiff distancePositive (power + 1)).of_le (by simp)).comp
      ((extensionSmooth.comp contDiff_fst).sub contDiff_snd)
  have regularized := path.domain_complex_spacetime_integral_contDiffAt inside function (fderiv ℝ function)
    functionSmooth.continuous (functionSmooth.continuous_fderiv (by norm_num))
    (fun point => (functionSmooth.differentiable (by norm_num) point).hasFDerivAt)
  apply regularized.congr_of_eventuallyEq
  filter_upwards [agreement, separatedNear] with parameter same separated
  apply setIntegral_congr_fun (path.domain_isOpen parameter).measurableSet
  intro position member
  dsimp only [function]
  rw [same]
  exact ((Section6.smoothConjugateInversePower_eventuallyEq distancePositive (power + 1)
    (separated position member)).self_of_nhds).symm

namespace FiniteMovingPatchFamily

theorem exteriorTaylorCoefficient_contDiffAt_of_local_center {count : ℕ}
    (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center : ℝ → ℂ) (radius : ℝ) (power : ℕ) {time : ℝ}
    (centerSmooth : ContDiffAt ℝ 1 center time)
    (inside : ∀ source ∈ selected, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (distance : Fin count → ℝ) (positive : ∀ source ∈ selected, 0 < distance source)
    (separatedNear : ∀ᶠ parameter in 𝓝 time, ∀ source ∈ selected,
      ∀ position ∈ (family.patch source).domain parameter, distance source ≤ ‖center parameter - position‖) :
    ContDiffAt ℝ 1 (family.exteriorTaylorCoefficient selected center radius power) time := by
  have individual (source : Fin count) (member : source ∈ selected) :=
    ((family.patch source).domain_conjugate_inverse_power_contDiffAt_of_local_center (inside source member)
      (positive source member) center centerSmooth (separatedNear.mono fun _ separated => separated source member) power).const_smul
        (family.density source)
  exact contDiffAt_const.mul (ContDiffAt.sum individual)

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
