import EulerNonuniqueness.Section3.RelabeledForcingPrimitiveSeries

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

theorem relabeledExteriorAmplitudeDerivativePrimitive_norm_le {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count)
    (angular : PeriodicC1HolderHalf) (angularSmall : ‖angular‖ < 1 / 2)
    {frequency time distance weight mass : ℝ} (nonzero : frequency ≠ 0)
    (inside : time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (centered : (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass)
    (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (weightBound : (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight)
    (massBound : (∫ position, |family.patchVorticity time index position|) ≤ mass) :
    ‖fixedRelabelEquivalence angular angularSmall
      (family.exteriorAmplitudeDerivativePrimitive index frequency time)‖ ≤
      1472 * weight ^ 2 / (Real.pi ^ 2 * |frequency|) +
        192 * mass * weight / (Real.pi ^ 2 * distance ^ 2 * |frequency|) := by
  refine (fixedRelabelEquivalence_norm_bound angular angularSmall _).trans ?_
  have estimate := mul_le_mul_of_nonneg_left
    (family.exteriorAmplitudeDerivativePrimitive_norm_le index nonzero inside material centered positive
      weightNonnegative massNonnegative small separated weightBound massBound) (by norm_num : (0 : ℝ) ≤ 8)
  convert estimate using 1 <;> ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
