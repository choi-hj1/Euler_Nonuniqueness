import EulerNonuniqueness.Section3.FiniteMovingPatchMotion
import EulerNonuniqueness.Section3.MovingMaterialPatchGeometricContinuity
import EulerNonuniqueness.Section6.BoundaryQuadrupoleComplexMoment

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem MovingMaterialPatch.continuous_domain_complex_spacetime_integral (path : MovingMaterialPatch)
    (function : ℝ × ℂ → ℂ) (continuous : Continuous function) :
    Continuous (fun time => ∫ position in path.domain time, function (time, position)) := by
  have realContinuous := path.continuous_domain_spacetime_integral (fun point => (function point).re)
    (Complex.continuous_re.comp continuous)
  have imaginaryContinuous := path.continuous_domain_spacetime_integral (fun point => (function point).im)
    (Complex.continuous_im.comp continuous)
  have result := (Complex.continuous_ofReal.comp realContinuous).add
    ((Complex.continuous_ofReal.comp imaginaryContinuous).mul
      (continuous_const : Continuous (fun _ : ℝ => Complex.I)))
  convert result using 1
  funext time
  exact (setIntegral_re_add_im (path.integral_continuous_function time
    (continuous.comp (continuous_const.prodMk continuous_id)))).symm

theorem MovingMaterialPatch.centroid_continuous (path : MovingMaterialPatch) : Continuous path.centroid := by
  have area := path.continuous_domain_area.inv₀ (fun time => (path.domain_area_positive time).ne')
  have moment := path.continuous_domain_complex_spacetime_integral (fun point => point.2) continuous_snd
  exact area.smul moment

namespace FiniteMovingPatchFamily

theorem patchCentroid_continuous {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (index : Fin count) (patch : Fin 4) :
    Continuous (fun time => Paper.patchCentroid family.patchMotion time index patch) := by
  have identity : (fun time => Paper.patchCentroid family.patchMotion time index patch) =
      (family.patch (finProdFinEquiv (index, patch))).centroid :=
    funext fun time => family.patchCentroid_eq time index patch
  rw [identity]
  exact (family.patch (finProdFinEquiv (index, patch))).centroid_continuous

theorem quadrupoleCenter_continuous {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (index : Fin count) : Continuous (fun time => quadrupoleCenter family.patchMotion time index) := by
  exact (continuous_finset_sum Finset.univ fun patch _ => family.patchCentroid_continuous index patch).div_const 4

theorem quadrupole_complex_moment_continuous {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (scales : Scales) (index : Fin count) :
    Continuous (fun time => ∫ position, quadrupoleDensity scales family.patchMotion time index position •
      (position - quadrupoleCenter family.patchMotion time index) ^ 2) := by
  have integrand : Continuous (fun point : ℝ × ℂ =>
      (point.2 - quadrupoleCenter family.patchMotion point.1 index) ^ 2) :=
    (continuous_snd.sub ((family.quadrupoleCenter_continuous index).comp continuous_fst)).pow 2
  have individual (patch : Fin 4) :=
    ((family.patch (finProdFinEquiv (index, patch))).continuous_domain_complex_spacetime_integral
      (fun point => (point.2 - quadrupoleCenter family.patchMotion point.1 index) ^ 2) integrand).const_smul
        (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
  have result := continuous_finset_sum Finset.univ fun patch _ => individual patch
  convert result using 1
  funext time
  exact integral_quadrupoleDensity_smul_of_bounded_domains scales family.patchMotion time index
    (fun patch => (family.patch (finProdFinEquiv (index, patch))).domain_isOpen time)
    (fun patch => (family.patch (finProdFinEquiv (index, patch))).domain_isBounded time)
    (fun position => (position - quadrupoleCenter family.patchMotion time index) ^ 2)
    ((continuous_id.sub continuous_const).pow 2)

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
