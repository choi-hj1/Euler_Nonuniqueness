import EulerNonuniqueness.Section6.PhysicalPointOrbit
import EulerNonuniqueness.Section6.TwoDipoleDynamics

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

def negativeLabelSwap : Equiv.Perm (Fin 4) := Equiv.swap 2 3

def relabelNegativePoints (positions : FourPointConfiguration) : FourPointConfiguration :=
  fun target => positions (negativeLabelSwap target)

theorem negativeLabelSwap_sign (target : Fin 4) :
    fourPointSign (negativeLabelSwap target) = fourPointSign target := by
  fin_cases target <;> simp [negativeLabelSwap, Equiv.swap_apply_def] <;> rfl

theorem relabelNegativePoints_involutive (positions : FourPointConfiguration) :
    relabelNegativePoints (relabelNegativePoints positions) = positions := by
  funext target
  simp [relabelNegativePoints, negativeLabelSwap]

theorem relabelNegativePoints_norm (positions : FourPointConfiguration) :
    ‖relabelNegativePoints positions‖ = ‖positions‖ := by
  have bound (current : FourPointConfiguration) : ‖relabelNegativePoints current‖ ≤ ‖current‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg current)).mpr
    intro target
    exact norm_le_pi_norm current (negativeLabelSwap target)
  apply le_antisymm (bound positions)
  simpa only [relabelNegativePoints_involutive] using bound (relabelNegativePoints positions)

theorem relabelNegativePoints_distance (positions reference : FourPointConfiguration) :
    ‖relabelNegativePoints positions - relabelNegativePoints reference‖ = ‖positions - reference‖ :=
  relabelNegativePoints_norm (positions - reference)

theorem relabelNegativePoints_central (positive negative : ℂ) :
    relabelNegativePoints (centrallySymmetricFourPoint positive negative) =
      centrallySymmetricFourPoint positive (-negative) := by
  funext target
  fin_cases target <;> simp [relabelNegativePoints, negativeLabelSwap, Equiv.swap_apply_def,
    centrallySymmetricFourPoint]

theorem fourPointField_negativeLabelSwap (coefficient : ℝ) (positions : FourPointConfiguration) :
    fourPointField coefficient (relabelNegativePoints positions) =
      relabelNegativePoints (fourPointField coefficient positions) := by
  funext target
  fin_cases target <;>
    simp [fourPointField, relabelNegativePoints, negativeLabelSwap, Equiv.swap_apply_def,
      fourPointSign, Fin.sum_univ_succ] <;> ring <;> simp

theorem physicalSeparatingPointOrbit_paper_labels (orbit : SeparatingOrbit)
    (frequency length : ℝ) (direction center : ℂ) (timeShift time : ℝ) (target : Fin 4) :
    physicalSeparatingPointOrbit orbit frequency length direction center timeShift time
        (negativeLabelSwap target) =
      center + (length : ℂ) * direction *
        centrallySymmetricFourPoint (orbit.positive (frequency * time + timeShift))
          (orbit.negative (frequency * time + timeShift)) target := by
  fin_cases target <;> simp [physicalSeparatingPointOrbit, negativeLabelSwap, Equiv.swap_apply_def,
    centrallySymmetricFourPoint]

theorem relabelNegativePoints_hasDerivAt {trajectory : ℝ → FourPointConfiguration}
    {coefficient time : ℝ}
    (equation : HasDerivAt trajectory (fourPointField coefficient (trajectory time)) time) :
    HasDerivAt (fun current => relabelNegativePoints (trajectory current))
      (fourPointField coefficient (relabelNegativePoints (trajectory time))) time := by
  rw [fourPointField_negativeLabelSwap]
  apply hasDerivAt_pi.mpr
  intro target
  exact hasDerivAt_pi.mp equation (negativeLabelSwap target)

theorem relabelNegativePoints_noncollision {positions : FourPointConfiguration}
    (noncollision : FourPointNoncollision positions) : FourPointNoncollision (relabelNegativePoints positions) := by
  intro target source different
  exact noncollision (negativeLabelSwap target) (negativeLabelSwap source)
    (fun equality => different (negativeLabelSwap.injective equality))

theorem paperPhysicalSeparatingPointOrbit_actual_equation (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) (frequency length : ℝ) (direction center : ℂ)
    (timeShift time : ℝ) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1) :
    HasDerivAt (fun current => relabelNegativePoints
      (physicalSeparatingPointOrbit orbit frequency length direction center timeShift current))
      (fourPointField (frequency * length ^ 2) (relabelNegativePoints
        (physicalSeparatingPointOrbit orbit frequency length direction center timeShift time))) time ∧
      FourPointNoncollision (relabelNegativePoints
        (physicalSeparatingPointOrbit orbit frequency length direction center timeShift time)) := by
  have properties := physicalSeparatingPointOrbit_actual_equation orbit normalized frequency length direction center
    timeShift time lengthPositive directionNorm
  exact ⟨relabelNegativePoints_hasDerivAt properties.1, relabelNegativePoints_noncollision properties.2⟩

theorem separatingInitialCenter_eq_physical_orbit (scales : Scales) (orbit : SeparatingOrbit)
    (sectionTime dipoleAngle : ℝ) (index : ℕ) (target : Fin 4) :
    separatingInitialCenter scales orbit sectionTime dipoleAngle index target =
      physicalSeparatingPointOrbit orbit 1 (scales.length index)
        (Complex.exp (Complex.I * (dipoleAngle - orbit.limitingDipoleAngle : ℝ)))
        (scales.location index : ℂ) sectionTime 0 (negativeLabelSwap target) := by
  rw [physicalSeparatingPointOrbit_paper_labels]
  fin_cases target <;> simp [separatingInitialCenter, centrallySymmetricFourPoint]

def relabelNegativePatchMotion {count : ℕ} (motion : PatchMotion count) : PatchMotion count where
  domain := fun time index patch => motion.domain time index (negativeLabelSwap patch)
  boundary := fun time index patch => motion.boundary time index (negativeLabelSwap patch)

theorem patchCentroid_negativeLabelSwap {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (patch : Fin 4) :
    patchCentroid (relabelNegativePatchMotion motion) time index patch =
      patchCentroid motion time index (negativeLabelSwap patch) := rfl

theorem patchDensity_negativeLabelSwap {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (patch : Fin 4) :
    patchDensity scales (relabelNegativePatchMotion motion) time index patch =
      patchDensity scales motion time index (negativeLabelSwap patch) := by
  have sign : patchSign (negativeLabelSwap patch) = patchSign patch := negativeLabelSwap_sign patch
  unfold patchDensity relabelNegativePatchMotion
  rw [sign]

theorem quadrupoleDensity_negativeLabelSwap {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) :
    quadrupoleDensity scales (relabelNegativePatchMotion motion) time index =
      quadrupoleDensity scales motion time index := by
  funext position
  simp only [quadrupoleDensity, patchDensity_negativeLabelSwap, Fin.sum_univ_succ]
  simp [negativeLabelSwap, Equiv.swap_apply_def]
  ring

theorem patchVorticity_negativeLabelSwap {count : ℕ} (scales : Scales) (motion : PatchMotion count) :
    patchVorticity scales (relabelNegativePatchMotion motion) = patchVorticity scales motion := by
  funext time position
  unfold patchVorticity
  exact Finset.sum_congr rfl fun index _ =>
    congrFun (quadrupoleDensity_negativeLabelSwap scales motion time index) position

theorem paper_pairCenterDistance_negativeLabelSwap {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) :
    pairCenterDistance motion time index =
      ‖(patchCentroid (relabelNegativePatchMotion motion) time index 0 +
          patchCentroid (relabelNegativePatchMotion motion) time index 2) / 2 -
        (patchCentroid (relabelNegativePatchMotion motion) time index 1 +
          patchCentroid (relabelNegativePatchMotion motion) time index 3) / 2‖ := by
  simp [pairCenterDistance, patchCentroid_negativeLabelSwap, negativeLabelSwap, Equiv.swap_apply_def]

end EulerNonuniqueness.Section6
