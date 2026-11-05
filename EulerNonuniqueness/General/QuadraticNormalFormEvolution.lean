import EulerNonuniqueness.General.QuadraticNormalFormForcing
import EulerNonuniqueness.General.QuadraticCoordinateInverse

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem quadratic_normalForm_forced_hasDerivAt
    (generator : Space →L[ℝ] Space) (quadratic correction resonant : BilinearEnd Space)
    {frequency time : ℝ} {trajectory : ℝ → Space} {remainder forcing : Space}
    (frequencyNonzero : frequency ≠ 0)
    (homological : quadraticCommutator generator correction = quadratic - resonant)
    (equation : HasDerivAt trajectory
      (frequency • generator (trajectory time) + quadratic (trajectory time) (trajectory time) + (remainder + forcing)) time) :
    HasDerivAt (fun current => quadraticCoordinate correction frequency (trajectory current))
      (frequency • generator (quadraticCoordinate correction frequency (trajectory time)) +
        resonant (quadraticCoordinate correction frequency (trajectory time))
          (quadraticCoordinate correction frequency (trajectory time)) +
        ((remainder + forcing - (1 / frequency : ℝ) •
          (correction (quadratic (trajectory time) (trajectory time) + (remainder + forcing)) (trajectory time) +
            correction (trajectory time) (quadratic (trajectory time) (trajectory time) + (remainder + forcing)))) +
          (resonant (trajectory time) (trajectory time) -
            resonant (quadraticCoordinate correction frequency (trajectory time))
              (quadraticCoordinate correction frequency (trajectory time))))) time := by
  have changed := quadratic_coordinate_hasDerivAt generator quadratic correction resonant frequencyNonzero homological equation
  convert changed using 1 <;> abel

end EulerNonuniqueness.General
