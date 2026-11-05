import EulerNonuniqueness.General.ProjectedQuadraticFamilyDerivative

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem scaled_projected_family_residual_identity
    (projection generator : Space →L[ℝ] Space) (quadratic : Space → BilinearEnd Space)
    (field : Space → Space) (frequency : ℝ) (parameter : Space) :
    projection (frequency • field parameter) - (frequency • generator) (projection parameter) -
      (frequency • quadratic parameter) (projection parameter) (projection parameter) =
      frequency • (projection (field parameter) - generator (projection parameter) -
        quadratic parameter (projection parameter) (projection parameter)) := by
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_sub]

theorem quadraticCommutator_generator_smul
    (generator : Space →L[ℝ] Space) (correction : BilinearEnd Space) (scalar : ℝ) :
    quadraticCommutator (scalar • generator) correction = scalar • quadraticCommutator generator correction := by
  ext first second
  change -(scalar • generator (correction first second)) + correction (scalar • generator first) second +
    correction first (scalar • generator second) =
    scalar • (-generator (correction first second) + correction (generator first) second + correction first (generator second))
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_add, smul_neg]

theorem projected_quadratic_family_scaled_hasDerivAt
    (projection generator : Space →L[ℝ] Space)
    (quadratic correction : Space → BilinearEnd Space) (field : Space → Space)
    (homological : ∀ parameter, quadraticCommutator generator (correction parameter) = quadratic parameter)
    (frequency : ℝ) {trajectory : ℝ → Space} {time : ℝ} {forcing : Space}
    (equation : HasDerivAt trajectory (frequency • field (trajectory time) + forcing) time) :
    let value := projection (trajectory time)
    let remainder := projection (frequency • field (trajectory time)) - (frequency • generator) value -
      (frequency • quadratic (trajectory time)) value value + projection forcing
    HasDerivAt (fun current => quadraticCoordinate (correction (trajectory time)) 1 (projection (trajectory current)))
      ((frequency • generator) (quadraticCoordinate (correction (trajectory time)) 1 value) +
        (remainder - (correction (trajectory time)
            ((frequency • quadratic (trajectory time)) value value + remainder) value +
          correction (trajectory time) value ((frequency • quadratic (trajectory time)) value value + remainder)))) time := by
  have scaled : ∀ parameter, quadraticCommutator (frequency • generator) (correction parameter) =
      frequency • quadratic parameter := by
    intro parameter
    rw [quadraticCommutator_generator_smul, homological]
  exact projected_quadratic_family_hasDerivAt projection (frequency • generator)
    (fun parameter => frequency • quadratic parameter) correction (fun value => frequency • field value)
    scaled equation

end EulerNonuniqueness.General
