import EulerNonuniqueness.Section5.ReferenceInteriorTubeOn

namespace EulerNonuniqueness.Section5

theorem reference_saddle_face_signs
    {rate decay radius quadratic forcingBound unstable stable unstableForcing stableForcing : ℝ}
    (radiusNonnegative : 0 ≤ radius) (quadraticNonnegative : 0 ≤ quadratic)
    (rateLower : decay ≤ rate)
    (unstableBound : |unstable| ≤ radius) (stableBound : |stable| ≤ radius)
    (forcingEstimate : |unstableForcing| + |stableForcing| ≤
      quadratic * (|unstable| + |stable|) ^ 2 + forcingBound)
    (small : 4 * quadratic * radius ^ 2 + forcingBound ≤ decay * radius / 2) :
    (unstable = radius → decay * radius / 2 ≤ rate * unstable + unstableForcing) ∧
      (unstable = -radius → rate * unstable + unstableForcing ≤ -(decay * radius / 2)) ∧
      (stable = radius → -rate * stable + stableForcing ≤ -(decay * radius / 2)) ∧
      (stable = -radius → decay * radius / 2 ≤ -rate * stable + stableForcing) := by
  have sumNonnegative : 0 ≤ |unstable| + |stable| := by positivity
  have squareBound : (|unstable| + |stable|) ^ 2 ≤ 4 * radius ^ 2 := by nlinarith
  have quadraticBound := mul_le_mul_of_nonneg_left squareBound quadraticNonnegative
  have totalBound : |unstableForcing| + |stableForcing| ≤ decay * radius / 2 := by nlinarith
  have rateRadius := mul_le_mul_of_nonneg_right rateLower radiusNonnegative
  constructor
  · intro onFace
    rw [onFace]
    nlinarith [neg_abs_le unstableForcing, abs_nonneg stableForcing]
  constructor
  · intro onFace
    rw [onFace]
    nlinarith [le_abs_self unstableForcing, abs_nonneg stableForcing]
  constructor
  · intro onFace
    rw [onFace]
    nlinarith [le_abs_self stableForcing, abs_nonneg unstableForcing]
  · intro onFace
    rw [onFace]
    nlinarith [neg_abs_le stableForcing, abs_nonneg unstableForcing]

theorem reference_actual_saddle_face_derivatives
    {unstable stable : ℝ → ℝ} {time rate decay radius quadratic forcingBound unstableForcing stableForcing : ℝ}
    (radiusNonnegative : 0 ≤ radius) (quadraticNonnegative : 0 ≤ quadratic)
    (rateLower : decay ≤ rate)
    (unstableBound : |unstable time| ≤ radius) (stableBound : |stable time| ≤ radius)
    (forcingEstimate : |unstableForcing| + |stableForcing| ≤
      quadratic * (|unstable time| + |stable time|) ^ 2 + forcingBound)
    (small : 4 * quadratic * radius ^ 2 + forcingBound ≤ decay * radius / 2)
    (unstableEquation : HasDerivAt unstable (rate * unstable time + unstableForcing) time)
    (stableEquation : HasDerivAt stable (-rate * stable time + stableForcing) time) :
    (unstable time = radius → decay * radius / 2 ≤ deriv unstable time) ∧
      (unstable time = -radius → deriv unstable time ≤ -(decay * radius / 2)) ∧
      (stable time = radius → deriv stable time ≤ -(decay * radius / 2)) ∧
      (stable time = -radius → decay * radius / 2 ≤ deriv stable time) := by
  rw [unstableEquation.deriv, stableEquation.deriv]
  exact reference_saddle_face_signs radiusNonnegative quadraticNonnegative rateLower
    unstableBound stableBound forcingEstimate small

end EulerNonuniqueness.Section5
