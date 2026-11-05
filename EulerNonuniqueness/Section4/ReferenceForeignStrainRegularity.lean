import EulerNonuniqueness.Section4.ReferenceForeignStrainGeometry
import EulerNonuniqueness.Section6.ForeignStrainRegularity

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem reference_foreign_strain_derivative_continuousOn {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) (index : Fin count) (times : Set ℝ)
    (densityEquation : ∀ (source : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (source, patch)) =
      patchSign patch * scales.amplitude * scales.omega (source.val + 1) ^ 4)
    (radiusEquation : ∀ (source : Fin count) (patch : Fin 4),
      (family.patch (finProdFinEquiv (source, patch))).radius = scales.radius (source.val + 1))
    (lengthSmall : ∀ source : Fin count, scales.length (source.val + 1) ≤ scales.location (source.val + 1) / 1000)
    (radiusSmall : ∀ source : Fin count, scales.radius (source.val + 1) ≤ scales.length (source.val + 1) / 1000)
    (inside : ∀ time ∈ times, ∀ source,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (material : ∀ time ∈ times, ∀ source label,
      (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label))
    (geometry : ∀ time ∈ times, ReferenceCentroidFieldGeometry scales family.patchMotion time index) :
    ContinuousOn (family.foreignQuadrupoleStrainDerivative scales index) times := by
  apply family.foreignQuadrupoleStrainDerivative_continuousOn scales index times densityEquation inside
    (fun time member source _ => material time member source) (fun _ => scales.location (index.val + 1) / 48)
  · intro time member
    exact div_pos (scales.location_pos _) (by norm_num)
  · intro time member
    exact family.reference_foreign_source_center_gaps scales radiusEquation lengthSmall radiusSmall index (geometry time member)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
