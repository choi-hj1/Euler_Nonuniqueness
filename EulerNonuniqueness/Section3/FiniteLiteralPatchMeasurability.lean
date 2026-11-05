import EulerNonuniqueness.Section3.NearCircleFamilyAngles
import EulerNonuniqueness.Section3.FiniteLiteralPatchFlow
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem measurable_polarInterior_indicator_joint (profile : ℝ → ℝ → ℝ)
    (profile_measurable : Measurable (Function.uncurry profile)) :
    Measurable (fun pair : ℝ × ℂ => (polarInterior (profile pair.1)).indicator (fun _ => (1 : ℝ)) pair.2) := by
  have radius_measurable : Measurable (fun pair : ℝ × ℂ => profile pair.1 (Complex.arg pair.2)) :=
    profile_measurable.comp (measurable_fst.prodMk (Complex.measurable_arg.comp measurable_snd))
  have domain_measurable : MeasurableSet {pair : ℝ × ℂ | pair.2 ∈ polarInterior (profile pair.1)} :=
    measurableSet_lt continuous_snd.norm.measurable radius_measurable
  have joint_indicator : Measurable
      ({pair : ℝ × ℂ | pair.2 ∈ polarInterior (profile pair.1)}.indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator domain_measurable
  convert joint_indicator using 1

theorem measurable_nearCircleInterior_indicator_joint
    (shape : ℝ → PeriodicC1HolderHalf) (shape_continuous : Continuous shape)
    (small : ∀ parameter, ‖shape parameter - standardCircleBanach‖ < 1 / 3) :
    Measurable (fun pair : ℝ × ℂ =>
      (nearCircleInterior (shape pair.1) (small pair.1)).indicator (fun _ => (1 : ℝ)) pair.2) := by
  exact measurable_polarInterior_indicator_joint
    (fun parameter angle => nearCircleRadialProfile (shape parameter) (small parameter) angle)
    (continuous_nearCircleRadialProfile_joint shape shape_continuous small).measurable

theorem affinePatchDomain_mem_iff (center : ℂ) {radius : ℝ} (positive : 0 < radius)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) (position : ℂ) :
    position ∈ affinePatchDomain center radius data small ↔
      (contourAffineHomeomorph center positive).symm position ∈ nearCircleInterior data small := by
  change position ∈ (contourAffineHomeomorph center positive) '' nearCircleInterior data small ↔ _
  constructor
  · rintro ⟨original, membership, rfl⟩
    simpa only [Homeomorph.symm_apply_apply] using membership
  · intro membership
    exact ⟨_, membership, (contourAffineHomeomorph center positive).apply_symm_apply position⟩

theorem measurable_affinePatchDomain_indicator_joint
    (center : ℂ) {radius : ℝ} (positive : 0 < radius)
    (shape : ℝ → PeriodicC1HolderHalf) (shape_continuous : Continuous shape)
    (small : ∀ parameter, ‖shape parameter - standardCircleBanach‖ < 1 / 3) :
    Measurable (fun pair : ℝ × ℂ =>
      (affinePatchDomain center radius (shape pair.1) (small pair.1)).indicator (fun _ => (1 : ℝ)) pair.2) := by
  have composed := (measurable_nearCircleInterior_indicator_joint shape shape_continuous small).comp
    (continuous_fst.prodMk ((contourAffineHomeomorph center positive).symm.continuous.comp continuous_snd)).measurable
  convert composed using 1
  funext pair
  dsimp only [Function.comp_apply]
  have membership := affinePatchDomain_mem_iff center positive (shape pair.1) (small pair.1) pair.2
  by_cases inside : pair.2 ∈ affinePatchDomain center radius (shape pair.1) (small pair.1)
  · rw [indicator_of_mem inside, indicator_of_mem (membership.mp inside)]
  · rw [indicator_of_not_mem inside, indicator_of_not_mem (fun member => inside (membership.mpr member))]

theorem FiniteLiteralPatchFlow.measurable_vorticity_joint {count : ℕ}
    {configuration : FiniteContourConfiguration count} (flow : FiniteLiteralPatchFlow configuration) :
    Measurable (fun pair : ℝ × ℂ => flow.vorticity pair.1 pair.2) := by
  dsimp only [FiniteLiteralPatchFlow.vorticity, FiniteContourConfiguration.literalVorticity]
  apply Finset.measurable_sum
  intro index _
  exact measurable_const.mul (measurable_affinePatchDomain_indicator_joint (configuration.center index)
    (configuration.radius_pos index) (fun parameter => flow.shape parameter index)
    ((continuous_apply index).comp flow.continuous)
    (fun parameter => (flow.nearby parameter index).trans_le (min_le_left _ _)))

end

end EulerNonuniqueness.Paper
