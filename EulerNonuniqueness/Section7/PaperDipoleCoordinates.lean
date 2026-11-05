import EulerNonuniqueness.Section7.QuadrupoleAnnulus
import EulerNonuniqueness.Section6.TwoDipoleDynamics

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def dipolePatchPermutation : Equiv.Perm (Fin 4) := Equiv.swap 2 3

theorem dipolePatchPermutation_apply (patch : Fin 4) :
    dipolePatchPermutation patch = ![(0 : Fin 4), 1, 3, 2] patch := by
  fin_cases patch <;> decide

def firstDipoleSeparation {count : ℕ} (motion : PatchMotion count) (time : ℝ) (index : Fin count) : ℂ :=
  patchCentroid motion time index 0 - patchCentroid motion time index 3

def secondDipoleSeparation {count : ℕ} (motion : PatchMotion count) (time : ℝ) (index : Fin count) : ℂ :=
  patchCentroid motion time index 1 - patchCentroid motion time index 2

theorem dipolePatchPermutation_sign (patch : Fin 4) :
    fourPointSign (dipolePatchPermutation patch) = fourPointSign patch := by
  fin_cases patch <;> norm_num [dipolePatchPermutation_apply, fourPointSign] <;> decide

theorem twoDipoleConfiguration_patchCentroids {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (patch : Fin 4) :
    twoDipoleConfiguration (firstDipoleCenter motion time index) (secondDipoleCenter motion time index)
      (firstDipoleSeparation motion time index) (secondDipoleSeparation motion time index) patch =
        patchCentroid motion time index (dipolePatchPermutation patch) := by
  fin_cases patch <;>
    norm_num [twoDipoleConfiguration, firstDipoleCenter, secondDipoleCenter,
      firstDipoleSeparation, secondDipoleSeparation, dipolePatchPermutation_apply] <;> ring

theorem fourPointField_dipolePatchPermutation (coefficient : ℝ) (positions : FourPointConfiguration)
    (patch : Fin 4) :
    fourPointField coefficient (fun label => positions (dipolePatchPermutation label)) patch =
      fourPointField coefficient positions (dipolePatchPermutation patch) := by
  fin_cases patch <;>
    simp [fourPointField, fourPointSign, dipolePatchPermutation_apply, Fin.sum_univ_succ] <;> ring <;> simp_all

end EulerNonuniqueness.Paper
