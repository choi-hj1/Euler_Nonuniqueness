import EulerNonuniqueness.General.LocalC1Extension
import EulerNonuniqueness.Section6.MovingExteriorTaylorCoefficient

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem exteriorTaylorCoefficient_hasDerivAt_of_local_center {count : ℕ}
    (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center : ℝ → ℂ) (radius : ℝ) (power : ℕ) {time : ℝ}
    (centerSmooth : ContDiffAt ℝ 1 center time)
    (inside : ∀ source ∈ selected,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (material : ∀ source ∈ selected, ∀ label,
      (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label))
    (distance : Fin count → ℝ) (positive : ∀ source ∈ selected, 0 < distance source)
    (separatedNear : ∀ᶠ parameter in 𝓝 time, ∀ source ∈ selected,
      ∀ position ∈ (family.patch source).domain parameter,
        distance source ≤ ‖center parameter - position‖) :
    HasDerivAt (family.exteriorTaylorCoefficient selected center radius power)
      (((-1 : ℂ) ^ (power + 1) * Complex.I * ((power + 1 : ℕ) : ℂ) *
          (radius : ℂ) ^ (power - 1) / ((2 * Real.pi : ℝ) : ℂ)) *
        ∑ source ∈ selected, family.density source • ∫ position in (family.patch source).domain time,
          star (deriv center time - biotSavart (family.vorticity time) position) *
            (star (center time - position))⁻¹ ^ (power + 2)) time := by
  obtain ⟨extension, velocity, extensionContinuous, velocityContinuous, equation, agreement⟩ :=
    General.exists_global_c1_extension_of_contDiffAt centerSmooth
  have atTime : extension time = center time := agreement.self_of_nhds
  have velocityAtTime : velocity time = deriv center time :=
    ((equation time).congr_of_eventuallyEq agreement.symm).deriv.symm
  have extensionSeparated : ∀ᶠ parameter in 𝓝 time, ∀ source ∈ selected,
      ∀ position ∈ (family.patch source).domain parameter,
        distance source ≤ ‖extension parameter - position‖ := by
    filter_upwards [agreement, separatedNear] with parameter same separated
    simpa only [same] using separated
  have actual := family.exteriorTaylorCoefficient_hasDerivAt selected extension velocity radius power
    extensionContinuous velocityContinuous equation inside material distance positive extensionSeparated
  have coefficientAgreement : family.exteriorTaylorCoefficient selected center radius power =ᶠ[𝓝 time]
      family.exteriorTaylorCoefficient selected extension radius power := by
    filter_upwards [agreement] with parameter same
    simp only [exteriorTaylorCoefficient, same]
  have result := actual.congr_of_eventuallyEq coefficientAgreement
  simpa only [atTime, velocityAtTime] using result

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
