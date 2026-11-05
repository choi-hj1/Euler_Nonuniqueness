import EulerNonuniqueness.Section6.ActualQuadrupolePatchDynamics

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointOddPart_add (first second : FourPointConfiguration) :
    fourPointOddPart (first + second) = fourPointOddPart first + fourPointOddPart second := by
  ext <;> simp [fourPointOddPart] <;> ring

theorem fourPointTotalOddForcing_add (coefficient : ℝ)
    (positions forcing residual : FourPointConfiguration) :
    fourPointTotalOddForcing coefficient positions (forcing + residual) =
      fourPointTotalOddForcing coefficient positions forcing + fourPointOddPart residual := by
  change fourPointOddInternalError coefficient positions + fourPointOddPart (forcing + residual) = _
  rw [fourPointOddPart_add]
  exact (add_assoc _ _ _).symm

theorem pointShapeForcing_patch_residual_bound (point : ℂ × ℂ)
    (positions forcing residual : FourPointConfiguration) (coefficient : ℝ) :
    ‖pointShapeForcing point.1 point.2
        (fourPointTotalOddForcing coefficient positions (forcing + residual)).1
        (fourPointTotalOddForcing coefficient positions (forcing + residual)).2 -
      pointShapeForcing point.1 point.2
        (fourPointTotalOddForcing coefficient positions forcing).1
        (fourPointTotalOddForcing coefficient positions forcing).2‖ ≤
      pointShapeForcingWeight point * ‖residual‖ := by
  rw [fourPointTotalOddForcing_add]
  simp only [Prod.fst_add, Prod.snd_add]
  rw [pointShapeForcing_add, add_sub_cancel_left]
  have estimate := pointShapeForcing_norm_bound point.1 point.2
    (fourPointOddPart residual).1 (fourPointOddPart residual).2
  change ‖pointShapeForcing point.1 point.2
    (fourPointOddPart residual).1 (fourPointOddPart residual).2‖ ≤ _
  exact estimate.trans (mul_le_mul_of_nonneg_left
    (fourPointOddPart_norm_le residual) (pointShapeForcingWeight_nonnegative point))

theorem forcedQuadrupole_odd_strain_decomposition {count : ℕ}
    (coefficients : Fin count → ℝ) (sources : FiniteQuadrupoleConfiguration count)
    (block : Fin count) (center : ℂ) (residual : FourPointConfiguration)
    (noncollision : ∀ sourceBlock, sourceBlock ≠ block → ∀ source,
      center - sources (sourceBlock, source) ≠ 0) :
    let positions := quadrupoleBlock sources block
    let point := fourPointOddPart positions
    let field := quadrupoleBlockExternalField coefficients sources block
    let strain := quadrupoleBlockExternalStrain coefficients sources block center
    fourPointTotalOddForcing (coefficients block) positions
        ((fun target => field (positions target)) + residual) =
      (strain * star point.1, strain * star point.2) +
        (fourPointOddInternalError (coefficients block) positions +
          fourPointOddPart (fourPointExternalTaylorRemainder field center
            (fderiv ℝ field center) positions) + fourPointOddPart residual) := by
  dsimp only
  rw [fourPointTotalOddForcing_add]
  change fourPointOddInternalError _ _ + fourPointOddPart _ + _ = _
  rw [quadrupoleBlockExternalField_odd_taylor coefficients sources block center _ noncollision]
  abel

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

theorem actual_patch_shape_forcing_deformation_bound {count : ℕ}
    {configuration : FiniteContourConfiguration count}
    (flow : FiniteLiteralPatchFlow configuration) {time : ℝ}
    (inside : time ∈ Set.Ioo (-flow.duration) flow.duration)
    (small : ∀ index, ‖flow.shape time index - standardCircleBanach‖ ≤ 1 / 16)
    (receivers : Fin 4 → Fin count)
    (separated : ∀ target source, source ≠ receivers target →
      8 * configuration.radius source ≤ ‖flow.centroid time (receivers target) - flow.centroid time source‖ ∧
      4 * configuration.radius (receivers target) ≤
        ‖flow.centroid time (receivers target) - flow.centroid time source‖)
    (point : ℂ × ℂ) (positions forcing : Section6.FourPointConfiguration)
    (coefficient : ℝ) :
    let residual := fun target => flow.centroidPointResidual time (receivers target)
    let envelope := fun target : Fin 4 =>
      ∑ source ∈ Finset.univ.erase (receivers target),
        128 * |configuration.density source * (Real.pi * configuration.radius source ^ 2)| *
          (8 * configuration.radius source ^ 2 * ‖flow.shape time source - standardCircleBanach‖ +
            configuration.radius (receivers target) ^ 2 *
              ‖flow.shape time (receivers target) - standardCircleBanach‖) /
          (Real.pi * ‖flow.centroid time (receivers target) - flow.centroid time source‖ ^ 3)
    ‖Section6.pointShapeForcing point.1 point.2
        (Section6.fourPointTotalOddForcing coefficient positions (forcing + residual)).1
        (Section6.fourPointTotalOddForcing coefficient positions (forcing + residual)).2 -
      Section6.pointShapeForcing point.1 point.2
        (Section6.fourPointTotalOddForcing coefficient positions forcing).1
        (Section6.fourPointTotalOddForcing coefficient positions forcing).2‖ ≤
      Section6.pointShapeForcingWeight point * ‖envelope‖ := by
  dsimp only
  apply (Section6.pointShapeForcing_patch_residual_bound point positions forcing _ coefficient).trans
  apply mul_le_mul_of_nonneg_left _ (Section6.pointShapeForcingWeight_nonnegative point)
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro target
  have estimate := flow.centroidPointResidual_relative_deformation_bound inside small
    (receivers target) (separated target)
  apply estimate.trans
  apply (le_abs_self _).trans
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm
    (fun receiver : Fin 4 =>
      ∑ source ∈ Finset.univ.erase (receivers receiver),
        128 * |configuration.density source * (Real.pi * configuration.radius source ^ 2)| *
          (8 * configuration.radius source ^ 2 * ‖flow.shape time source - standardCircleBanach‖ +
            configuration.radius (receivers receiver) ^ 2 *
              ‖flow.shape time (receivers receiver) - standardCircleBanach‖) /
          (Real.pi * ‖flow.centroid time (receivers receiver) - flow.centroid time source‖ ^ 3)) target

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
