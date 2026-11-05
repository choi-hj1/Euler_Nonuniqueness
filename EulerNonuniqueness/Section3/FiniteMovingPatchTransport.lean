import EulerNonuniqueness.Section3.FiniteMovingPatchBounds
import EulerNonuniqueness.General.WeakTransportFiniteSum

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem passive_weakTransportOn (family : FiniteMovingPatchFamily count) {horizon : ℝ}
    (nonnegative : 0 ≤ horizon)
    (initialInside : ∀ index, (family.patch index).initialTime < 0)
    (finalInside : ∀ index, horizon < (family.patch index).finalTime)
    (material : ∀ time ∈ Icc 0 horizon, ∀ index label,
      (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label)) (index : Fin count) :
    WeakTransportOn horizon (family.patchVorticity 0 index) (fun time => family.patchVorticity time index)
      (fun time => biotSavart (family.vorticity time)) := by
  obtain ⟨speed, speedNonnegative, speedBound⟩ := family.exists_uniform_speed_bound nonnegative
  exact (family.patch index).passive_density_weakTransportOn nonnegative (initialInside index) (finalInside index)
    family.vorticity (fun time _ => family.vorticity_integrable time)
    (fun time _ => family.vorticity_memLp time _) (fun time inside label => material time inside index label)
    family.measurable_biotSavart speedNonnegative
    (fun time inside position => speedBound time ⟨inside.1.le, inside.2.le⟩ position) (family.density index)

theorem weakTransportOn (family : FiniteMovingPatchFamily count) {horizon : ℝ}
    (nonnegative : 0 ≤ horizon)
    (initialInside : ∀ index, (family.patch index).initialTime < 0)
    (finalInside : ∀ index, horizon < (family.patch index).finalTime)
    (material : ∀ time ∈ Icc 0 horizon, ∀ index label,
      (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label)) :
    WeakTransportOn horizon (family.vorticity 0) family.vorticity (fun time => biotSavart (family.vorticity time)) := by
  exact weakTransportOn_fintype_sum (family.patchVorticity 0) (fun index time => family.patchVorticity time index)
    (fun time => biotSavart (family.vorticity time)) (family.passive_weakTransportOn nonnegative initialInside finalInside material)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
