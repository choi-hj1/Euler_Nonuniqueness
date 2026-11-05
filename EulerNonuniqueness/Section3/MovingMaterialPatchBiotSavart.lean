import EulerNonuniqueness.Section3.FiniteMovingPatchBiotSavart
import EulerNonuniqueness.Section3.SimilarityPatchBiotSavart
import EulerNonuniqueness.Section3.ComplexHolderInstances

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

local instance movingPhysicalContourComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf :=
  Submodule.normedSpace complexPeriodicC1HolderGraph

namespace MovingMaterialPatch

def physicalContour (path : MovingMaterialPatch) (time : ℝ) : PeriodicC1HolderHalf :=
  c1AffineContour (path.center time) path.radius ((Circle.exp (path.phase time) : ℂ) • path.shape time)

theorem physicalContour_value (path : MovingMaterialPatch) (time label : ℝ) :
    (path.physicalContour time).val.1 label = path.boundary time label := rfl

theorem physicalContour_tangent (path : MovingMaterialPatch) (time label : ℝ) :
    (path.physicalContour time).val.2.val.1 label =
      path.radius • ((Circle.exp (path.phase time) : ℂ) * (path.shape time).val.2.val.1 label) := by
  change 0 + path.radius • ((Circle.exp (path.phase time) : ℂ) * (path.shape time).val.2.val.1 label) = _
  exact zero_add _

theorem integral_domain_kernel_eq_pointContour (path : MovingMaterialPatch) (time : ℝ)
    (chordSmall : ‖path.shape time - standardCircleBanach‖ < 2 / (3 * Real.pi)) (position : ℂ) :
    (∫ source in path.domain time, biotSavartKernel (position - source)) =
      pointContourVelocity (path.physicalContour time).val.1 (path.physicalContour time).val.2.val.1 position (-Real.pi) Real.pi := by
  have actual := integral_similarityPatchDomain_biotSavart_all_points (path.center time) path.radius_positive
    (Circle.exp (path.phase time)) (path.shape time) (path.nearby time) chordSmall position
  have tangentIdentity : (fun label => path.radius •
      ((Circle.exp (path.phase time) : ℂ) * (path.shape time).val.2.val.1 label)) =
      (path.physicalContour time).val.2.val.1 := by
    funext label
    exact (path.physicalContour_tangent time label).symm
  rw [tangentIdentity] at actual
  exact actual

end MovingMaterialPatch

theorem FiniteMovingPatchFamily.biotSavart_eq_sum_physical_contours {count : ℕ}
    (family : FiniteMovingPatchFamily count) (time : ℝ)
    (chordSmall : ∀ index, ‖(family.patch index).shape time - standardCircleBanach‖ < 2 / (3 * Real.pi)) (position : ℂ) :
    biotSavart (family.vorticity time) position =
      ∑ index, family.density index • pointContourVelocity ((family.patch index).physicalContour time).val.1
        ((family.patch index).physicalContour time).val.2.val.1 position (-Real.pi) Real.pi := by
  rw [family.biotSavart_eq_sum_domain_integrals]
  apply Finset.sum_congr rfl
  intro index _member
  rw [(family.patch index).integral_domain_kernel_eq_pointContour time (chordSmall index) position]

end EulerNonuniqueness.Paper
