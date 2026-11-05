import EulerNonuniqueness.General.QuadraticCoordinateChange

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem projected_frozen_quadratic_hasDerivAt
    (projection generator : Space →L[ℝ] Space) (quadratic correction : BilinearEnd Space)
    (field : Space → Space) {trajectory : ℝ → Space} {time : ℝ} {forcing : Space}
    (homological : quadraticCommutator generator correction = quadratic)
    (equation : HasDerivAt trajectory (field (trajectory time) + forcing) time) :
    let value := projection (trajectory time)
    let remainder := projection (field (trajectory time)) - generator value - quadratic value value + projection forcing
    HasDerivAt (fun current => quadraticCoordinate correction 1 (projection (trajectory current)))
      (generator (quadraticCoordinate correction 1 value) +
        (remainder - (correction (quadratic value value + remainder) value +
          correction value (quadratic value value + remainder)))) time := by
  let value := projection (trajectory time)
  let remainder := projection (field (trajectory time)) - generator value - quadratic value value + projection forcing
  have projected : HasDerivAt (fun current => projection (trajectory current))
      (generator value + quadratic value value + remainder) time := by
    have derivative : HasFDerivAt (projection : Space → Space) projection (trajectory time) :=
      ContinuousLinearMap.hasFDerivAt projection
    have actual := HasFDerivAt.comp_hasDerivAt (E := Space) (F := Space)
      (f := trajectory) time derivative equation
    convert actual using 1
    dsimp only [remainder]
    rw [map_add]
    abel
  have identity : quadraticCommutator generator correction = quadratic - 0 := by
    simpa only [sub_zero] using homological
  have actual := quadratic_coordinate_hasDerivAt generator quadratic correction 0
    (frequency := 1) (by norm_num) identity (by simpa only [one_smul] using projected)
  simp only [one_div_one, one_smul, ContinuousLinearMap.zero_apply, zero_add, add_zero] at actual
  convert actual using 1
  dsimp only [value, remainder]
  abel

end EulerNonuniqueness.General
