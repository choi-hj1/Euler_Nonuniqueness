import EulerNonuniqueness.General.CubicSpectralIntertwiner

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem scalar_annihilates_intertwined_spectral_projection
    (scalar : Space →L[ℝ] ℝ) (operator reference coordinates projection : Space →L[ℝ] Space)
    (projectionIdentity : projection = cubicSpectralProjection reference)
    (intertwines : operator.comp coordinates = coordinates.comp reference)
    (annihilates : ∀ value, scalar (operator value) = 0) (direction : Space) :
    scalar (coordinates (projection direction)) = 0 := by
  rw [projectionIdentity]
  change scalar (coordinates ((-4 : ℝ) • reference (reference direction))) = 0
  rw [map_smul, map_smul]
  have pointwise := congrArg (fun linear : Space →L[ℝ] Space => linear (reference direction)) intertwines
  change operator (coordinates (reference direction)) = coordinates (reference (reference direction)) at pointwise
  rw [← pointwise, annihilates, smul_zero]

end EulerNonuniqueness.General
