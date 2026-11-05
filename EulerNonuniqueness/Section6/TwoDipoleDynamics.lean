import EulerNonuniqueness.Section6.DipoleInteraction

noncomputable section

namespace EulerNonuniqueness.Section6

def twoDipoleConfiguration (firstCenter secondCenter firstSeparation secondSeparation : ℂ) : FourPointConfiguration :=
  ![firstCenter + firstSeparation / 2, secondCenter + secondSeparation / 2,
    firstCenter - firstSeparation / 2, secondCenter - secondSeparation / 2]

def dipoleCrossCenterVelocity (coefficient : ℝ) (sourceCenter targetCenter sourceSeparation targetSeparation : ℂ) : ℂ :=
  (neutralPairVelocity coefficient sourceCenter sourceSeparation (targetCenter + targetSeparation / 2) +
    neutralPairVelocity coefficient sourceCenter sourceSeparation (targetCenter - targetSeparation / 2)) / 2

def dipoleCrossRelativeVelocity (coefficient : ℝ) (sourceCenter targetCenter sourceSeparation targetSeparation : ℂ) : ℂ :=
  neutralPairVelocity coefficient sourceCenter sourceSeparation (targetCenter + targetSeparation / 2) -
    neutralPairVelocity coefficient sourceCenter sourceSeparation (targetCenter - targetSeparation / 2)

theorem fourPointField_twoDipoles (coefficient : ℝ)
    (firstCenter secondCenter firstSeparation secondSeparation : ℂ) :
    fourPointField coefficient (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) =
      ![-Complex.I * (coefficient : ℂ) / star firstSeparation +
          neutralPairVelocity coefficient secondCenter secondSeparation (firstCenter + firstSeparation / 2),
        -Complex.I * (coefficient : ℂ) / star secondSeparation +
          neutralPairVelocity coefficient firstCenter firstSeparation (secondCenter + secondSeparation / 2),
        -Complex.I * (coefficient : ℂ) / star firstSeparation +
          neutralPairVelocity coefficient secondCenter secondSeparation (firstCenter - firstSeparation / 2),
        -Complex.I * (coefficient : ℂ) / star secondSeparation +
          neutralPairVelocity coefficient firstCenter firstSeparation (secondCenter - secondSeparation / 2)] := by
  funext target
  fin_cases target <;>
    simp [fourPointField, twoDipoleConfiguration, fourPointSign, Fin.sum_univ_succ, neutralPairVelocity,
      star_sub, star_add, star_div₀, star_ofNat] <;>
      simp only [← Complex.star_def, star_ofNat] <;> ring_nf

theorem twoDipole_first_pair_equations {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {coefficient time : ℝ}
    (equation : ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField coefficient (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time)) target) time) :
    HasDerivAt firstCenter (-Complex.I * (coefficient : ℂ) / star (firstSeparation time) +
        dipoleCrossCenterVelocity coefficient (secondCenter time) (firstCenter time)
          (secondSeparation time) (firstSeparation time)) time ∧
      HasDerivAt firstSeparation
        (dipoleCrossRelativeVelocity coefficient (secondCenter time) (firstCenter time)
          (secondSeparation time) (firstSeparation time)) time := by
  have firstEquation := equation 0
  have secondEquation := equation 2
  rw [fourPointField_twoDipoles] at firstEquation secondEquation
  simp only [twoDipoleConfiguration, Matrix.cons_val_zero, Matrix.cons_val_succ] at firstEquation secondEquation
  constructor
  · convert (firstEquation.add secondEquation).div_const 2 using 1
    · funext current
      dsimp
      ring
    · dsimp [dipoleCrossCenterVelocity]
      ring
  · convert firstEquation.sub secondEquation using 1
    · funext current
      dsimp
      ring
    · dsimp [dipoleCrossRelativeVelocity]
      ring

theorem dipoleCrossCenterVelocity_bound (coefficient : ℝ)
    {sourceCenter targetCenter sourceSeparation targetSeparation : ℂ}
    (distancePositive : 0 < ‖targetCenter - sourceCenter‖)
    (separationBound : ‖sourceSeparation‖ + ‖targetSeparation‖ ≤ ‖targetCenter - sourceCenter‖) :
    ‖dipoleCrossCenterVelocity coefficient sourceCenter targetCenter sourceSeparation targetSeparation‖ ≤
      4 * |coefficient| * ‖sourceSeparation‖ / ‖targetCenter - sourceCenter‖ ^ 2 :=
  neutralPairVelocity_average_bound coefficient distancePositive separationBound

theorem dipoleCrossRelativeVelocity_bound (coefficient : ℝ)
    {sourceCenter targetCenter sourceSeparation targetSeparation : ℂ}
    (distancePositive : 0 < ‖targetCenter - sourceCenter‖)
    (separationBound : ‖sourceSeparation‖ + ‖targetSeparation‖ ≤ ‖targetCenter - sourceCenter‖) :
    ‖dipoleCrossRelativeVelocity coefficient sourceCenter targetCenter sourceSeparation targetSeparation‖ ≤
      32 * |coefficient| * ‖sourceSeparation‖ * ‖targetSeparation‖ / ‖targetCenter - sourceCenter‖ ^ 3 :=
  neutralPairVelocity_relative_bound coefficient distancePositive separationBound

end EulerNonuniqueness.Section6
