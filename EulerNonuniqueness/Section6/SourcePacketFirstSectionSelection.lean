import EulerNonuniqueness.Section5.NormalizedSeparatingCandidateOutgoingFirstSections
import EulerNonuniqueness.Section6.SourcePacketTerminalSectionSelection

noncomputable section
open Set
namespace EulerNonuniqueness.Section6
open EulerNonuniqueness.Paper EulerNonuniqueness.Section2

/-- A single explicit normalized model supplies transverse first sections with signed-window accuracy. -/
theorem normalizedSeparatingCandidate_exists_with_signed_first_sections :
    ∃ timeShift rotationPhase dipoleAngle : ℝ, ∃ offset : ℂ,
    let orbit := separatingCandidate timeShift rotationPhase dipoleAngle offset
    let modelDerivative := fun time : ℝ =>
      separatingRadiusScalarVelocity (separatingScalarOrbit 1 (by norm_num) (time + timeShift))
    IsNormalizedSeparatingOrbit orbit ∧
      ∃ factor > (0 : ℝ), factor ≤ 1 / 100 ∧
        (∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
          2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) target -
            centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) source‖) ∧
        ∀ tolerance : ℝ, 0 < tolerance → ∀ radiusMin : ℝ,
        ∃ sectionTime : ℝ, 1 < sectionTime ∧
        ∃ initialError > (0 : ℝ), initialError ≤ 1 / 64 ∧
          max 2048 radiusMin ≤ separationRadius orbit sectionTime ∧
          (∀ time ∈ Icc (sectionTime - 1) (sectionTime + 1),
            HasDerivAt (separationRadius orbit) (modelDerivative time) time ∧ 1 ≤ modelDerivative time) ∧
          (∀ time ≤ sectionTime - 1, separationRadius orbit time ≤ separationRadius orbit sectionTime - 1) ∧
          ‖orbit.positive sectionTime + orbit.negative sectionTime -
            Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ initialError / 2 ∧
          (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
            (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
              (orbit.positive sectionTime - orbit.negative sectionTime)).re ∧
          20 * initialError + 83200 / separationRadius orbit sectionTime ^ 2 ≤
            min (tolerance / 4) 1 / 5120 := by
  obtain ⟨timeShift, rotationPhase, dipoleAngle, offset, normalized, factor, factorPositive,
    factorSmall, separated, firstSections⟩ := normalizedSeparatingCandidate_exists_with_outgoing_first_sections
  let orbit := separatingCandidate timeShift rotationPhase dipoleAngle offset
  refine ⟨timeShift, rotationPhase, dipoleAngle, offset, normalized, factor, factorPositive,
    factorSmall, separated, ?_⟩
  intro tolerance tolerancePositive radiusMin
  let budget := min (tolerance / 4) 1 / 5120
  have budgetPositive : 0 < budget := by dsimp only [budget]; positivity
  let initialError := min (1 / 64) (budget / 40)
  have errorPositive : 0 < initialError := by dsimp only [initialError]; positivity
  have errorSmall : initialError ≤ 1 / 64 := min_le_left _ _
  have errorBudget : 20 * initialError ≤ budget / 2 := by
    have bound : initialError ≤ budget / 40 := min_le_right _ _
    linarith only [bound]
  obtain ⟨sectionTime, timeLarge, radiusBound, derivative, earlierMargin, close, outgoing⟩ :=
    firstSections initialError errorPositive errorSmall (max (max 2048 radiusMin) (166400 / budget + 1))
  have radiusLarge : max 2048 radiusMin ≤ separationRadius orbit sectionTime :=
    (le_max_left _ _).trans ((le_max_right _ _).trans radiusBound)
  have radiusBudget : 166400 / budget + 1 ≤ separationRadius orbit sectionTime :=
    (le_max_right _ _).trans ((le_max_right _ _).trans radiusBound)
  have radiusPositive : 0 < separationRadius orbit sectionTime := by
    have large := (le_max_left (2048 : ℝ) radiusMin).trans radiusLarge
    linarith only [large]
  have radiusOne : 1 ≤ separationRadius orbit sectionTime := by
    have large := (le_max_left (2048 : ℝ) radiusMin).trans radiusLarge
    linarith only [large]
  have budgetProduct : 166400 ≤ budget * separationRadius orbit sectionTime := by
    have lower : 166400 / budget ≤ separationRadius orbit sectionTime := by
      linarith only [radiusBudget]
    exact (div_le_iff₀ budgetPositive).mp lower |>.trans_eq (mul_comm _ _)
  have radiusSquare : separationRadius orbit sectionTime ≤ separationRadius orbit sectionTime ^ 2 := by
    nlinarith only [radiusOne]
  have squareBudget : 166400 ≤ budget * separationRadius orbit sectionTime ^ 2 :=
    budgetProduct.trans (mul_le_mul_of_nonneg_left radiusSquare budgetPositive.le)
  have reciprocalBudget : 83200 / separationRadius orbit sectionTime ^ 2 ≤ budget / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos radiusPositive)).mpr
    nlinarith only [squareBudget]
  refine ⟨sectionTime, timeLarge, initialError, errorPositive, errorSmall, radiusLarge,
    derivative, earlierMargin, close, outgoing, ?_⟩
  change 20 * initialError + 83200 / separationRadius orbit sectionTime ^ 2 ≤ budget
  linarith only [errorBudget, reciprocalBudget]

end EulerNonuniqueness.Section6
