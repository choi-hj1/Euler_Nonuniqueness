import EulerNonuniqueness.Section6.PaperExteriorCoefficientDerivative
import EulerNonuniqueness.Section6.PaperAngularMomentDynamics

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

def externalQuadrupoleStrainDerivative {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (index : Fin count) (time : ℝ) : ℂ :=
  (Complex.I / (Real.pi : ℂ)) * ∫ position,
    externalPatchVorticity scales motion time index position •
      (star (((∑ patch : Fin 4, patchAverageVelocity scales motion time index patch
          (biotSavart (patchVorticity scales motion time))) / 4) -
        biotSavart (patchVorticity scales motion time) position) *
        (star (quadrupoleCenter motion time index - position))⁻¹ ^ 3)

theorem FinitePatchEvolution.externalQuadrupoleStrain_hasDerivAt_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonPositive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (separated : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    (index : Fin count) (inside : time ∈ Ioo 0 horizon)
    {distance : ℝ} (distancePositive : 0 < distance)
    (separatedNear : ∀ᶠ current in 𝓝 time, ∀ source ∈ Finset.univ.erase index, ∀ patch position,
      position ∈ motion.domain current source patch →
        distance ≤ ‖quadrupoleCenter motion current index - position‖) :
    HasDerivAt (externalQuadrupoleStrain scales motion (fun current => quadrupoleCenter motion current index) index)
      (externalQuadrupoleStrainDerivative scales motion index time) time := by
  have centerDerivative := evolution.quadrupoleCenter_hasDerivAt_of_boundary_gaps horizonPositive
    amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index inside
  have coefficientDerivative := evolution.hasDerivAt_external_inverse_power_of_boundary_gaps horizonPositive
    amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index inside centerDerivative
    distancePositive separatedNear 1
  have actual := coefficientDerivative.const_mul (-Complex.I / (2 * Real.pi : ℂ))
  convert actual using 1
  simp only [externalQuadrupoleStrainDerivative, Nat.reduceAdd, Nat.cast_ofNat]
  field_simp
  <;> ring

end EulerNonuniqueness.Paper
