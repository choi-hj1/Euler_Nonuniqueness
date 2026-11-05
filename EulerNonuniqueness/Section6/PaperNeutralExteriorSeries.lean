import EulerNonuniqueness.Section6.SignedExteriorSeriesRelative
import EulerNonuniqueness.Section6.PaperExternalStaticData
import EulerNonuniqueness.Section6.PaperReferenceShapeForcing

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def quadrupoleNormalizedCentroidOffsets {count : ℕ} (motion : PatchMotion count)
    (index : Fin count) (time radius : ℝ) : FourPointConfiguration :=
  fun patch => (radius : ℂ)⁻¹ * (patchCentroid motion time index patch - quadrupoleCenter motion time index)

theorem quadrupoleNormalizedCentroidOffsets_signed_average {count : ℕ} (motion : PatchMotion count)
    (index : Fin count) (time radius : ℝ) :
    fourPointSignedAverageCLM (quadrupoleNormalizedCentroidOffsets motion index time radius) =
      (radius : ℂ)⁻¹ * centroidAsymmetry motion time index := by
  rw [show quadrupoleNormalizedCentroidOffsets motion index time radius =
      (radius : ℂ)⁻¹ • ((fun patch => patchCentroid motion time index patch) -
        (fun _ => quadrupoleCenter motion time index)) from rfl,
    map_smul, map_sub, fourPointSignedAverageCLM_constant, sub_zero,
    fourPointSignedAverageCLM_apply, centroid_fourPointSignedMoment]
  simp only [smul_eq_mul]
  congr 1
  ring

def quadrupoleExternalPointAverage {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (index : Fin count) (time : ℝ) : ℂ :=
  fourPointSignedAverageCLM (fun patch =>
    biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index patch))

theorem FinitePatchEvolution.quadrupoleExternalPointAverage_signed_series
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) {radius distance : ℝ} (radiusPositive : 0 < radius) (distancePositive : 0 < distance)
    (separated : ∀ source ∈ Function.support (externalPatchVorticity scales motion time index),
      distance ≤ ‖quadrupoleCenter motion time index - source‖)
    (centroidsInside : ∀ patch, ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ < distance) :
    HasSum (fun power : ℕ =>
      exteriorVorticityCoefficient (externalPatchVorticity scales motion time index)
        (quadrupoleCenter motion time index) radius power *
          signedExteriorMoment (quadrupoleNormalizedCentroidOffsets motion index time radius) power)
      ((radius : ℂ)⁻¹ * quadrupoleExternalPointAverage scales motion index time) := by
  have normalized (patch : Fin 4) : radius *
      ‖quadrupoleNormalizedCentroidOffsets motion index time radius patch‖ =
      ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ := by
    simp only [quadrupoleNormalizedCentroidOffsets, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos radiusPositive]
    field_simp
  have actual := exterior_biotSavart_signed_series_hasSum
    (evolution.externalPatchVorticity_integrable inside index)
    (evolution.externalPatchVorticity_memLp inside index (ENNReal.ofReal (4 : ℝ)))
    (quadrupoleCenter motion time index) (quadrupoleNormalizedCentroidOffsets motion index time radius)
    radiusPositive distancePositive separated (fun patch =>
      (div_lt_one distancePositive).mpr (by rw [normalized]; exact centroidsInside patch))
  have evaluation (patch : Fin 4) : quadrupoleCenter motion time index + (radius : ℂ) *
      quadrupoleNormalizedCentroidOffsets motion index time radius patch = patchCentroid motion time index patch := by
    dsimp only [quadrupoleNormalizedCentroidOffsets]
    field_simp [Complex.ofReal_ne_zero.mpr radiusPositive.ne']
    <;> ring
  simpa only [quadrupoleExternalPointAverage, evaluation] using actual

end EulerNonuniqueness.Paper
