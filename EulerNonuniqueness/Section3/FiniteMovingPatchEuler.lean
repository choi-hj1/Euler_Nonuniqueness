import EulerNonuniqueness.Section3.FiniteMovingPatchEvolution
import EulerNonuniqueness.Section3.FinitePatchAnalytic

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem vorticity_support_of_domain_bound (family : FiniteMovingPatchFamily count) (time : ℝ) {radius : ℝ}
    (domainBound : ∀ index, (family.patch index).domain time ⊆ Metric.closedBall 0 radius) :
    Function.support (family.vorticity time) ⊆ Metric.closedBall 0 radius := by
  intro position supported
  by_contra outside
  have zero : family.vorticity time position = 0 := by
    unfold vorticity
    apply Finset.sum_eq_zero
    intro index _
    exact indicator_of_not_mem (fun member => outside (domainBound index member)) _
  exact supported zero

theorem isEulerSolutionOn_of_material_equation (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ (index : Fin count) (patch : Fin 4), (family.patch (finProdFinEquiv (index, patch))).radius =
      scales.radius (index.val + 1))
    {horizon : ℝ} (positive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (initialInside : ∀ index, (family.patch index).initialTime < 0)
    (finalInside : ∀ index, horizon < (family.patch index).finalTime)
    (initialArea : ∀ index, volume.real ((family.patch index).domain 0) = Real.pi * (family.patch index).radius ^ 2)
    (material : ∀ time ∈ Icc 0 horizon, ∀ index label,
      (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label)) :
    IsEulerSolutionOn horizon (family.vorticity 0) family.vorticity := by
  have evolution := family.finitePatchEvolution scales densityIdentity radiusIdentity positive.le initialInside finalInside initialArea material
  obtain ⟨radius, radiusPositive, domainBound⟩ := family.exists_uniform_domain_bound positive.le
  have supported : ∃ radius : ℝ, 0 < radius ∧ ∀ time ∈ Icc 0 horizon,
      Function.support (Paper.patchVorticity scales family.patchMotion time) ⊆ Metric.closedBall 0 radius := by
    refine ⟨radius, radiusPositive, ?_⟩
    intro time inside
    rw [family.patchVorticity_eq scales densityIdentity]
    exact family.vorticity_support_of_domain_bound time (domainBound time inside)
  have result := evolution.isEulerSolutionOn positive amplitudePositive frequencyPositive ratioPositive supported
  rw [family.patchVorticity_eq scales densityIdentity] at result
  exact result

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
