import EulerNonuniqueness.Section4.ReferenceForeignStrainGeometry
import EulerNonuniqueness.Section6.PaperExternalStrain

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem exteriorVorticityCoefficient_zero_eq_complexStrain (vorticity : Vorticity) (center : ℂ) (radius : ℝ) :
    exteriorVorticityCoefficient vorticity center radius 0 = vorticityComplexStrain vorticity center := by
  have identity : (fun source => vorticity source • biotSavartKernelStrain center source) =
      fun source => -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
        (vorticity source • (star (center - source))⁻¹ ^ 2) := by
    funext source
    simp only [biotSavartKernelStrain, Complex.real_smul, div_eq_mul_inv, inv_pow]
    ring
  rw [vorticityComplexStrain, identity, integral_const_mul]
  simp only [exteriorVorticityCoefficient, pow_zero, Nat.zero_add, pow_one, neg_one_mul, mul_one]
  congr 1
  ring

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem reference_foreign_strain_eq_complexStrain {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) (time : ℝ) (index : Fin count)
    (densityEquation : ∀ (source : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (source, patch)) =
      patchSign patch * scales.amplitude * scales.omega (source.val + 1) ^ 4)
    (geometry : ReferenceCentroidFieldGeometry scales family.patchMotion time index) :
    family.foreignQuadrupoleStrain index time =
      Section6.vorticityComplexStrain (externalPatchVorticity scales family.patchMotion time index)
        (quadrupoleCenter family.patchMotion time index) := by
  have positive : 0 < scales.location (index.val + 1) / 24 := div_pos (scales.location_pos _) (by norm_num)
  have separated : ∀ source ∈ foreignQuadrupolePatchLabels index, ∀ position ∈ (family.patch source).domain time,
      scales.location (index.val + 1) / 24 ≤ ‖quadrupoleCenter family.patchMotion time index - position‖ := by
    intro source member position positionInside
    obtain ⟨⟨sourceIndex, patch⟩, rfl⟩ := (finProdFinEquiv : Fin count × Fin 4 ≃ Fin (count * 4)).surjective source
    have different := (mem_foreignQuadrupolePatchLabels index sourceIndex patch).mp member
    have erased : sourceIndex ∈ Finset.univ.erase index := Finset.mem_erase.mpr ⟨different, Finset.mem_univ _⟩
    have differentIndices : index.val + 1 ≠ sourceIndex.val + 1 := fun equality =>
      different (Fin.ext (Nat.add_right_cancel equality).symm)
    have locations := scales.location_sum_le_three_distance differentIndices
    have actual := geometry.centerSeparated sourceIndex erased patch position positionInside
    dsimp only [referenceSourceDistance] at actual
    linarith [scales.location_pos (sourceIndex.val + 1)]
  rw [foreignQuadrupoleStrain, family.exteriorTaylorCoefficient_eq_vorticityCoefficient
    (foreignQuadrupolePatchLabels index) (fun current => quadrupoleCenter family.patchMotion current index) 1 time 0 positive separated,
    ← family.externalPatchVorticity_eq_subfamily scales densityEquation time index]
  exact Section6.exteriorVorticityCoefficient_zero_eq_complexStrain _ _ _

theorem reference_foreign_strain_is_biotSavart_derivative {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count)
    (densityEquation : ∀ (source : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (source, patch)) =
      patchSign patch * scales.amplitude * scales.omega (source.val + 1) ^ 4)
    (geometry : ReferenceCentroidFieldGeometry scales family.patchMotion time index) :
    HasFDerivAt (biotSavart (externalPatchVorticity scales family.patchMotion time index))
      (family.foreignQuadrupoleStrain index time • (Complex.conjCLE : ℂ →L[ℝ] ℂ))
      (quadrupoleCenter family.patchMotion time index) := by
  rw [family.reference_foreign_strain_eq_complexStrain scales time index densityEquation geometry]
  exact evolution.externalPatch_biotSavart_hasFDerivAt_complexStrain inside index
    (referenceSourceDistance scales index) geometry.positive geometry.centerSeparated

theorem reference_foreign_strain_phase_integral_eq {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) (index : Fin count)
    (phase : ℝ → ℝ) {terminal : ℝ} (terminalNonnegative : 0 ≤ terminal)
    (densityEquation : ∀ (source : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (source, patch)) =
      patchSign patch * scales.amplitude * scales.omega (source.val + 1) ^ 4)
    (geometry : ∀ time ∈ Icc 0 terminal, ReferenceCentroidFieldGeometry scales family.patchMotion time index) :
    (∫ time in (0 : ℝ)..terminal, family.foreignQuadrupoleStrain index time *
        Complex.exp (-2 * Complex.I * (phase time : ℂ))) =
      ∫ time in (0 : ℝ)..terminal,
        Section6.vorticityComplexStrain (externalPatchVorticity scales family.patchMotion time index)
          (quadrupoleCenter family.patchMotion time index) * Complex.exp (-2 * Complex.I * (phase time : ℂ)) := by
  apply intervalIntegral.integral_congr
  intro time member
  rw [uIcc_of_le terminalNonnegative] at member
  dsimp only
  rw [family.reference_foreign_strain_eq_complexStrain scales time index densityEquation (geometry time member)]

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
