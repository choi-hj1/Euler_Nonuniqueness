import EulerNonuniqueness.General.ProjectedFrozenQuadraticDerivative

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem projected_quadratic_family_hasDerivAt
    (projection generator : Space →L[ℝ] Space)
    (quadratic correction : Space → BilinearEnd Space) (field : Space → Space)
    (homological : ∀ parameter, quadraticCommutator generator (correction parameter) = quadratic parameter)
    {trajectory : ℝ → Space} {time : ℝ} {forcing : Space}
    (equation : HasDerivAt trajectory (field (trajectory time) + forcing) time) :
    let value := projection (trajectory time)
    let remainder := projection (field (trajectory time)) - generator value -
      quadratic (trajectory time) value value + projection forcing
    HasDerivAt (fun current => quadraticCoordinate (correction (trajectory time)) 1 (projection (trajectory current)))
      (generator (quadraticCoordinate (correction (trajectory time)) 1 value) +
        (remainder - (correction (trajectory time) (quadratic (trajectory time) value value + remainder) value +
          correction (trajectory time) value (quadratic (trajectory time) value value + remainder)))) time := by
  exact projected_frozen_quadratic_hasDerivAt projection generator
    (quadratic (trajectory time)) (correction (trajectory time)) field (homological (trajectory time)) equation

end EulerNonuniqueness.General
