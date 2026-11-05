import EulerNonuniqueness.Section5.CascadeStatement
import EulerNonuniqueness.Section4.ReferenceInitialVorticity
import EulerNonuniqueness.General.FiniteLpNormBounds

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem cascade_initial_difference_eq_last {count : ℕ} (scales : Scales)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) (dipoleAngle : ℕ → ℝ)
    (reference alternative : PatchMotion (count + 1))
    (initialDisks : CascadeInitialDisks scales orbit sectionTime dipoleAngle reference alternative) :
    patchVorticity scales alternative 0 - patchVorticity scales reference 0 =
      quadrupoleDensity scales alternative 0 (Fin.last count) -
        quadrupoleDensity scales reference 0 (Fin.last count) := by
  funext position
  change (∑ index : Fin (count + 1), quadrupoleDensity scales alternative 0 index position) -
    (∑ index : Fin (count + 1), quadrupoleDensity scales reference 0 index position) = _
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have prefixEqual : (∑ index : Fin count, quadrupoleDensity scales alternative 0 index.castSucc position) =
      ∑ index : Fin count, quadrupoleDensity scales reference 0 index.castSucc position := by
    apply Finset.sum_congr rfl
    intro index _
    rw [cascade_initial_quadrupole_agree scales orbit sectionTime dipoleAngle reference alternative initialDisks
      index.castSucc (by simpa only [Fin.coe_castSucc] using Nat.add_lt_add_right index.isLt 1)]
  rw [prefixEqual]
  simp only [Pi.sub_apply]
  ring

theorem cascade_initial_last_eq_disk {count : ℕ} (scales : Scales)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) (dipoleAngle : ℕ → ℝ)
    (reference alternative : PatchMotion (count + 1))
    (initialDisks : CascadeInitialDisks scales orbit sectionTime dipoleAngle reference alternative) :
    quadrupoleDensity scales alternative 0 (Fin.last count) =
      diskQuadrupoleDensity scales
        (fun _ patch => separatingInitialCenter scales orbit sectionTime (dipoleAngle (count + 1)) (count + 1) patch) count := by
  funext position
  simp only [quadrupoleDensity, diskQuadrupoleDensity, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro patch _
  unfold patchDensity diskDensity
  rw [(initialDisks.2 (Fin.last count) (by simp) patch).1]
  simp only [Fin.val_last]

theorem cascade_initial_difference_Lp_bound {count : ℕ} (scales : Scales)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) (dipoleAngle : ℕ → ℝ)
    (reference alternative : PatchMotion (count + 1))
    (initialDisks : CascadeInitialDisks scales orbit sectionTime dipoleAngle reference alternative)
    (phase unstable : Fin (count + 1) → ℝ) (threshold : ℝ)
    (referenceDisks : ReferenceInitialDisks scales reference phase unstable threshold)
    (amplitudePositive : 0 < scales.amplitude) {exponent : ℝ} (exponentBound : 1 ≤ exponent) :
    MemLp (patchVorticity scales alternative 0 - patchVorticity scales reference 0)
        (ENNReal.ofReal exponent) volume ∧
      (eLpNorm (patchVorticity scales alternative 0 - patchVorticity scales reference 0)
        (ENNReal.ofReal exponent) volume).toReal ≤
        8 * (scales.amplitude * scales.omega (count + 1) ^ 4 *
          (Real.pi * scales.radius (count + 1) ^ 2) ^ (1 / exponent)) := by
  have lpBound : 1 ≤ ENNReal.ofReal exponent := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal exponentBound
  letI : Fact (1 ≤ ENNReal.ofReal exponent) := ⟨lpBound⟩
  rw [cascade_initial_difference_eq_last scales orbit sectionTime dipoleAngle reference alternative initialDisks,
    cascade_initial_last_eq_disk scales orbit sectionTime dipoleAngle reference alternative initialDisks,
    reference_initial_quadrupole_eq_disk scales reference phase unstable threshold referenceDisks]
  simp only [Fin.val_last]
  refine ⟨(diskQuadrupoleDensity_memLp _ _ _ _).sub (diskQuadrupoleDensity_memLp _ _ _ _), ?_⟩
  calc
    _ ≤ _ := eLpNorm_toReal_sub_le (diskQuadrupoleDensity_memLp _ _ _ _) (diskQuadrupoleDensity_memLp _ _ _ _)
    _ ≤ _ := by
      have alternativeBound := diskQuadrupoleDensity_eLpNorm_toReal_le scales
        (fun _ patch => separatingInitialCenter scales orbit sectionTime (dipoleAngle (count + 1)) (count + 1) patch)
        count amplitudePositive exponentBound
      have referenceBound := diskQuadrupoleDensity_eLpNorm_toReal_le scales
        (referenceInitialCenters scales phase unstable) count amplitudePositive exponentBound
      linarith

theorem cascade_initial_difference_tendsto_zero (scales : Scales)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) (dipoleAngle : ℕ → ℕ → ℝ)
    (reference alternative : (count : ℕ) → PatchMotion (count + 1))
    (initialDisks : ∀ count, CascadeInitialDisks scales orbit sectionTime (dipoleAngle count) (reference count) (alternative count))
    (phase unstable : (count : ℕ) → Fin (count + 1) → ℝ) (threshold : ℝ)
    (referenceDisks : ∀ count, ReferenceInitialDisks scales (reference count) (phase count) (unstable count) threshold)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioGreaterOne : 1 < scales.ratio) (alphaPositive : 0 < scales.alpha)
    {exponent : ℝ} (exponentBound : 1 ≤ exponent) :
    Tendsto (fun count => eLpNorm (patchVorticity scales (alternative count) 0 -
      patchVorticity scales (reference count) 0) (ENNReal.ofReal exponent) volume) atTop (𝓝 0) := by
  have properties (count : ℕ) := cascade_initial_difference_Lp_bound scales orbit sectionTime (dipoleAngle count)
    (reference count) (alternative count) (initialDisks count) (phase count) (unstable count) threshold
    (referenceDisks count) amplitudePositive exponentBound
  have envelopeTendsto := (scales.patch_Lp_envelope_summable amplitudePositive frequencyPositive ratioGreaterOne
    alphaPositive (zero_lt_one.trans_le exponentBound)).tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1)
  have realConverges : Tendsto (fun count =>
      (eLpNorm (patchVorticity scales (alternative count) 0 - patchVorticity scales (reference count) 0)
        (ENNReal.ofReal exponent) volume).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun count => (properties count).2)
      (by simpa only [mul_zero] using envelopeTendsto.const_mul 8)
  have ennrealConverges := ENNReal.continuous_ofReal.continuousAt.tendsto.comp realConverges
  change Tendsto (fun count => ENNReal.ofReal
    (eLpNorm (patchVorticity scales (alternative count) 0 - patchVorticity scales (reference count) 0)
      (ENNReal.ofReal exponent) volume).toReal) atTop (𝓝 (ENNReal.ofReal 0)) at ennrealConverges
  have equal (count : ℕ) := ENNReal.ofReal_toReal (properties count).1.eLpNorm_lt_top.ne
  simpa only [equal, ENNReal.ofReal_zero] using ennrealConverges

end EulerNonuniqueness.Paper
