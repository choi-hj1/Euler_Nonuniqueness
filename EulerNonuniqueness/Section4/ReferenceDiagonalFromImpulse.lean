import EulerNonuniqueness.Section6.PaperPatchAngularInertia

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.reference_diagonal_impulse_error
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time error : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    (control : ∀ patch : Fin 4, BoundaryCloseToCircle scales motion time index patch error)
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 16) :
    |diagonalDifference motion time index / scales.length (index.val + 1) ^ 2 - 1| ≤
      |angularImpulse scales motion time index /
        (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) - 1| +
      48 * error ^ 2 / (scales.amplitude * scales.omega (index.val + 1) ^ 3) := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have denominatorPositive : 0 < 2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2 := by
    positivity
  have inertia := evolution.quadrupole_angular_inertia_bound_of_boundaryControl inside amplitudePositive
    frequencyPositive ratioPositive index control errorNonnegative errorSmall
  have normalized := div_le_div_of_nonneg_right inertia denominatorPositive.le
  rw [← abs_of_pos denominatorPositive, ← abs_div] at normalized
  have differenceIdentity : (angularImpulse scales motion time index -
      2 * scales.circulation (index.val + 1) * diagonalDifference motion time index) /
        (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) =
      angularImpulse scales motion time index /
        (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) -
      diagonalDifference motion time index / scales.length (index.val + 1) ^ 2 := by
    field_simp
    <;> ring
  rw [differenceIdentity] at normalized
  have errorIdentity : (48 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * error ^ 2) /
      (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) =
      48 * error ^ 2 / (scales.amplitude * scales.omega (index.val + 1) ^ 3) := by
    rw [scales.radius_sq amplitudePositive frequencyPositive ratioPositive]
    field_simp
    <;> ring
  rw [abs_of_pos denominatorPositive, errorIdentity] at normalized
  have triangle := abs_sub_le
    (diagonalDifference motion time index / scales.length (index.val + 1) ^ 2)
    (angularImpulse scales motion time index /
      (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2)) 1
  rw [abs_sub_comm] at normalized
  exact triangle.trans ((add_le_add_right normalized _).trans_eq (add_comm _ _))

end EulerNonuniqueness.Paper
