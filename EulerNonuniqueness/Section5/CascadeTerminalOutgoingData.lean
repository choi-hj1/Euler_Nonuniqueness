import EulerNonuniqueness.Section5.CascadeInitialSeparation
import EulerNonuniqueness.Section6.PhysicalOutgoingData
import EulerNonuniqueness.Section6.NegativeLabelBridge

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_cascade_terminal_outgoing_initial_data (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) :
    ∃ sectionTime > (0 : ℝ), 512 ≤ separationRadius orbit sectionTime ∧
    ∀ {count : ℕ} {scales : Scales} {horizon : ℝ} {dipoleAngle : ℕ → ℝ}
      {reference alternative : PatchMotion count},
    FinitePatchEvolution scales alternative horizon → 0 ≤ horizon →
    0 < scales.amplitude → 0 < scales.frequency → 0 < scales.ratio →
    CascadeInitialDisks scales orbit sectionTime dipoleAngle reference alternative →
    ∀ index : Fin count, index.val + 1 = count →
    let positions := relabelNegativePoints (fun patch => patchCentroid alternative 0 index patch)
    let direction := Complex.exp (Complex.I * (dipoleAngle count - orbit.limitingDipoleAngle : ℝ)) *
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))
    ‖positions 0 - positions 2 - (scales.length count : ℂ) * direction‖ ≤ scales.length count / 64 ∧
      ‖positions 1 - positions 3 - (scales.length count : ℂ) * (-direction)‖ ≤ scales.length count / 64 ∧
      (3 / 4 : ℝ) * scales.length count * separationRadius orbit sectionTime ≤
        (Complex.I * star direction * ((positions 0 + positions 2) / 2 -
          (positions 1 + positions 3) / 2)).re ∧
      ‖(positions 0 + positions 2) / 2 - (positions 1 + positions 3) / 2‖ ≤
        (5 / 4 : ℝ) * scales.length count * separationRadius orbit sectionTime := by
  obtain ⟨sectionTime, timePositive, radiusLarge, separationClose, outgoing⟩ :=
    normalizedSeparatingOrbit_arbitrary_outgoing_section orbit normalized
      (tolerance := 1 / 128) (by norm_num) 0
  refine ⟨sectionTime, timePositive, (le_max_left _ _).trans radiusLarge, ?_⟩
  intro count scales horizon dipoleAngle reference alternative evolution horizonNonnegative amplitudePositive
    frequencyPositive ratioPositive initial index last
  let positions := relabelNegativePoints (fun patch => patchCentroid alternative 0 index patch)
  let rotation := Complex.exp (Complex.I * (dipoleAngle count - orbit.limitingDipoleAngle : ℝ))
  have positionsIdentity : positions = fun target => (scales.location count : ℂ) +
      (scales.length count : ℂ) * rotation *
        centrallySymmetricFourPoint (orbit.positive sectionTime) (-orbit.negative sectionTime) target := by
    funext target
    dsimp only [positions, relabelNegativePoints]
    rw [evolution.cascade_terminal_initial_centroid horizonNonnegative amplitudePositive frequencyPositive
      ratioPositive initial index last, separatingInitialCenter_eq_physical_orbit]
    simp [physicalSeparatingPointOrbit, rotation, negativeLabelSwap]
  have close : ‖positions - (fun target => (scales.location count : ℂ) +
      (scales.length count : ℂ) * rotation *
        centrallySymmetricFourPoint (orbit.positive sectionTime) (-orbit.negative sectionTime) target)‖ ≤
      (1 / 64 : ℝ) * scales.length count / 4 := by
    rw [positionsIdentity, sub_self, norm_zero]
    exact div_nonneg (mul_nonneg (by norm_num) (scales.length_pos count).le) (by norm_num)
  have result := physical_outgoing_initial_data (positive := orbit.positive sectionTime)
    (negative := orbit.negative sectionTime) (direction := Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ)))
    (rotation := rotation) (center := (scales.location count : ℂ)) (positions := positions)
    (length := scales.length count) (error := 1 / 64) (scales.length_pos count) (by norm_num) (by norm_num)
    (by simp [Complex.norm_exp, Complex.mul_re]) (by simp [rotation, Complex.norm_exp, Complex.mul_re])
    ((le_max_left _ _).trans radiusLarge) (by convert separationClose using 1 <;> norm_num) outgoing close
  have scaled : (1 / 64 : ℝ) * scales.length count = scales.length count / 64 := by ring
  rw [scaled] at result
  simpa only [positions, rotation, separationRadius] using result

end EulerNonuniqueness.Paper
