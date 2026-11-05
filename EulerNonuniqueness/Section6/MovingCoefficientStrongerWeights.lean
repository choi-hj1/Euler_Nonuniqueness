import EulerNonuniqueness.Section6.TemporalCoefficientStrongerWeights
import EulerNonuniqueness.Section6.UniformExteriorCoefficientBounds

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem exteriorMaterialCoefficientDerivative_stronger_weight_bounds {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time distance weight mass factor : ℝ}
    (inside : time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (centered : (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass)
    (factorOne : 1 ≤ factor) (small : 8 * (factor * (family.patch index).radius) ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (weightBound : (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight)
    (massBound : (∫ position, |family.patchVorticity time index position|) ≤ mass) :
    Summable (fun power : ℕ => (2 * factor) ^ (power + 1) *
      ‖family.exteriorMaterialCoefficientDerivative index power time‖) ∧
    (∑' power : ℕ, (2 * factor) ^ (power + 1) *
      ‖family.exteriorMaterialCoefficientDerivative index power time‖) ≤
      factor * (46 * weight ^ 2 / Real.pi ^ 2 + 6 * mass * weight / (Real.pi ^ 2 * distance ^ 2)) := by
  have radiusPositive := (family.patch index).radius_positive
  have factorNonnegative : 0 ≤ factor := by linarith
  have radiusInflation : (family.patch index).radius ≤ factor * (family.patch index).radius := by
    nlinarith
  have geometrySmall : 4 * (family.patch index).radius ≤ distance := by linarith
  have ratioSmall : 4 * (factor * (family.patch index).radius) / distance < 1 :=
    (div_lt_one positive).mpr (by linarith)
  have envelopeSummable := summable_stronger_weight_temporalCoefficientEnvelope radiusPositive.le
    positive weightNonnegative massNonnegative factorOne ratioSmall
  have dominates (power : ℕ) :
      (2 * factor) ^ (power + 1) * ‖family.exteriorMaterialCoefficientDerivative index power time‖ ≤
      (2 * factor) ^ (power + 1) * temporalCoefficientEnvelope (family.patch index).radius distance weight mass power :=
    mul_le_mul_of_nonneg_left
      (family.norm_exteriorMaterialCoefficientDerivative_le_uniform index inside material centered positive
        geometrySmall separated weightBound massBound power) (by positivity)
  have actualSummable : Summable (fun power : ℕ => (2 * factor) ^ (power + 1) *
      ‖family.exteriorMaterialCoefficientDerivative index power time‖) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) dominates envelopeSummable
  refine ⟨actualSummable, ?_⟩
  exact (Summable.tsum_le_tsum dominates actualSummable envelopeSummable).trans
    (tsum_stronger_weight_temporalCoefficientEnvelope_le radiusPositive.le positive weightNonnegative
      massNonnegative factorOne small)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
