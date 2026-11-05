import EulerNonuniqueness.Section3.ContourCauchyOperator
import EulerNonuniqueness.Section3.HolderBanachAlgebraNorms

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

def holderConjugateCLM : PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf :=
  LinearMap.mkContinuous
    { toFun := holderConjugate
      map_add' := by
        intro first second
        apply PeriodicHolderHalf.ext_value
        intro label
        exact star_add _ _
      map_smul' := by
        intro scalar density
        apply PeriodicHolderHalf.ext_value
        intro label
        change star (scalar • density.val.1 label) = scalar • star (density.val.1 label)
        exact star_smul scalar _ }
    1 (fun density => by simpa using holderConjugate_norm_bound density)

theorem standardCircleBanach_near :
    ‖standardCircleBanach - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
  change max ‖standardCircleBanach.val.1 - standardCircleBanach.val.1‖
    ‖standardCircleBanach.val.2 - standardCircleBanach.val.2‖ < _
  simp only [sub_self, norm_zero, max_self]
  exact lt_min (by norm_num) (by positivity)

def circleCauchyCLM : PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf :=
  contourCauchyOperatorCLM standardCircleBanach standardCircleBanach_near

def periodicHilbertCLM : PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf :=
  (1 / (2 * Real.pi)) •
    (circleCauchyCLM + holderConjugateCLM.comp (circleCauchyCLM.comp holderConjugateCLM))

theorem periodicHilbertCLM_value (density : PeriodicHolderHalf) (target : ℝ) :
    (periodicHilbertCLM density).val.1 target =
      (1 / (2 * Real.pi)) •
        (contourCauchyTransform standardCircle standardCircleTangent density.val.1 target +
          star (contourCauchyTransform standardCircle standardCircleTangent
            (fun source => star (density.val.1 source)) target)) := rfl

def periodicHilbertBound : ℝ :=
  max (contourCauchySupConstant standardCircleBanach)
    (contourCauchyGlobalHolderConstant standardCircleBanach) / Real.pi

theorem periodicHilbertCLM_norm_bound (density : PeriodicHolderHalf) :
    ‖periodicHilbertCLM density‖ ≤ periodicHilbertBound * ‖density‖ := by
  let bound := max (contourCauchySupConstant standardCircleBanach)
    (contourCauchyGlobalHolderConstant standardCircleBanach)
  have nonnegative : 0 ≤ bound :=
    (contourCauchySupConstant_nonneg standardCircleBanach standardCircleBanach_near).trans
      (le_max_left _ _)
  have first : ‖circleCauchyCLM density‖ ≤ bound * ‖density‖ :=
    contourCauchyOperator_norm_bound standardCircleBanach standardCircleBanach_near density
  have second : ‖holderConjugateCLM (circleCauchyCLM (holderConjugateCLM density))‖ ≤
      bound * ‖density‖ := by
    apply (holderConjugate_norm_bound _).trans
    apply (contourCauchyOperator_norm_bound standardCircleBanach
      standardCircleBanach_near (holderConjugate density)).trans
    exact mul_le_mul_of_nonneg_left (holderConjugate_norm_bound density) nonnegative
  change ‖(1 / (2 * Real.pi)) •
    (circleCauchyCLM density + holderConjugateCLM (circleCauchyCLM (holderConjugateCLM density)))‖ ≤ _
  calc
    _ ≤ ‖(1 / (2 * Real.pi) : ℝ)‖ *
        ‖circleCauchyCLM density + holderConjugateCLM (circleCauchyCLM (holderConjugateCLM density))‖ :=
      norm_smul_le _ _
    _ = (1 / (2 * Real.pi)) *
        ‖circleCauchyCLM density + holderConjugateCLM (circleCauchyCLM (holderConjugateCLM density))‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
    _ ≤ (1 / (2 * Real.pi)) * (bound * ‖density‖ + bound * ‖density‖) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add first second)) (by positivity)
    _ = periodicHilbertBound * ‖density‖ := by
      unfold periodicHilbertBound
      dsimp only [bound]
      field_simp
      ring

theorem holderConjugate_involutive (density : PeriodicHolderHalf) :
    holderConjugate (holderConjugate density) = density := by
  apply PeriodicHolderHalf.ext_value
  intro label
  exact star_star _

theorem periodicHilbertCLM_conjugate (density : PeriodicHolderHalf) :
    periodicHilbertCLM (holderConjugate density) = holderConjugate (periodicHilbertCLM density) := by
  apply PeriodicHolderHalf.ext_value
  intro label
  rw [periodicHilbertCLM_value, holderConjugate_value, periodicHilbertCLM_value]
  simp only [holderConjugate_value, star_smul, star_add, star_star, star_trivial]
  rw [add_comm]
  rfl

theorem periodicHilbertCLM_real (density : PeriodicHolderHalf)
    (real : ∀ label, star (density.val.1 label) = density.val.1 label) (target : ℝ) :
    star ((periodicHilbertCLM density).val.1 target) =
      (periodicHilbertCLM density).val.1 target := by
  have conjugate : holderConjugate density = density := PeriodicHolderHalf.ext_value real
  have identity := periodicHilbertCLM_conjugate density
  rw [conjugate] at identity
  exact (congrArg (fun data : PeriodicHolderHalf => data.val.1 target) identity).symm

theorem circleCauchyCLM_shift (offset : ℝ) (density : PeriodicHolderHalf) :
    circleCauchyCLM (holderLabelShift offset density) =
      holderLabelShift offset (circleCauchyCLM density) := by
  apply PeriodicHolderHalf.ext_value
  intro target
  have identity := contourCauchyTransform_normalized_shift offset standardCircleBanach density target
  rw [normalizedContourShift_circle] at identity
  exact identity

theorem holderConjugate_shift (offset : ℝ) (density : PeriodicHolderHalf) :
    holderConjugate (holderLabelShift offset density) =
      holderLabelShift offset (holderConjugate density) := by
  apply PeriodicHolderHalf.ext_value
  intro target
  rfl

theorem periodicHilbertCLM_shift (offset : ℝ) (density : PeriodicHolderHalf) :
    periodicHilbertCLM (holderLabelShift offset density) =
      holderLabelShift offset (periodicHilbertCLM density) := by
  apply PeriodicHolderHalf.ext_value
  intro target
  have first := congrArg (fun data : PeriodicHolderHalf => data.val.1 target)
    (circleCauchyCLM_shift offset density)
  have second := congrArg (fun data : PeriodicHolderHalf => data.val.1 target)
    (circleCauchyCLM_shift offset (holderConjugate density))
  rw [← holderConjugate_shift] at second
  dsimp only at first second
  rw [periodicHilbertCLM_value, holderLabelShift_value, periodicHilbertCLM_value]
  change (1 / (2 * Real.pi)) •
    ((circleCauchyCLM (holderLabelShift offset density)).val.1 target +
      star ((circleCauchyCLM (holderConjugate (holderLabelShift offset density))).val.1 target)) = _
  rw [first, second]
  rfl

end

end EulerNonuniqueness.Paper
