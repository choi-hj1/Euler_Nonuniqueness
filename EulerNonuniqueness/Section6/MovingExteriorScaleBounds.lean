import EulerNonuniqueness.Section6.MovingExteriorPrimitiveBound

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem exteriorForcingPrimitive_norm_le_scaled {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count)
    {frequency time omega amplitude length coefficient : ℝ}
    (omegaPositive : 0 < omega) (amplitudePositive : 0 < amplitude) (lengthPositive : 0 < length)
    (coefficientNonnegative : 0 ≤ coefficient) (frequencyIdentity : |frequency| = amplitude * omega ^ 4)
    (small : 8 * (family.patch index).radius ≤ length / 100)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      length / 100 ≤ ‖(family.patch index).center time - position‖)
    (weightBound : (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤
        coefficient * omega) :
    ‖family.exteriorForcingPrimitive index frequency time‖ ≤
      (8 * coefficient / Real.pi) / (amplitude * omega ^ 3) := by
  have nonzero : frequency ≠ 0 := abs_pos.mp (frequencyIdentity ▸ by positivity)
  have geometrySmall : 4 * (family.patch index).radius ≤ length / 100 := by
    linarith [(family.patch index).radius_positive]
  have estimate := family.exteriorForcingPrimitive_norm_le index nonzero
    (div_pos lengthPositive (by norm_num)) (mul_nonneg coefficientNonnegative omegaPositive.le)
    geometrySmall separated weightBound
  rw [frequencyIdentity] at estimate
  convert estimate using 1 <;> field_simp <;> ring

theorem exteriorAmplitudeDerivativePrimitive_norm_le_scaled {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count)
    {frequency time omega amplitude length coefficient : ℝ}
    (omegaPositive : 0 < omega) (amplitudePositive : 0 < amplitude) (lengthPositive : 0 < length)
    (coefficientNonnegative : 0 ≤ coefficient) (frequencyIdentity : |frequency| = amplitude * omega ^ 4)
    (inside : time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (centered : (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid)
    (small : 8 * (family.patch index).radius ≤ length / 100)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      length / 100 ≤ ‖(family.patch index).center time - position‖)
    (weightBound : (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤
        coefficient * omega)
    (massBound : (∫ position, |family.patchVorticity time index position|) ≤
      2 * Real.pi * omega * length ^ 2) :
    ‖family.exteriorAmplitudeDerivativePrimitive index frequency time‖ ≤
      (184 * coefficient ^ 2 / Real.pi ^ 2 + 480000 * coefficient / Real.pi) / (amplitude * omega ^ 2) := by
  have nonzero : frequency ≠ 0 := abs_pos.mp (frequencyIdentity ▸ by positivity)
  have estimate := family.exteriorAmplitudeDerivativePrimitive_norm_le index nonzero inside material centered
    (div_pos lengthPositive (by norm_num)) (mul_nonneg coefficientNonnegative omegaPositive.le)
    (by positivity : 0 ≤ 2 * Real.pi * omega * length ^ 2) small separated weightBound massBound
  rw [frequencyIdentity] at estimate
  convert estimate using 1 <;> field_simp <;> ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
