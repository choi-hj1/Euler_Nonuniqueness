import EulerNonuniqueness.Section6.UniformTaylor

noncomputable section

namespace EulerNonuniqueness.Section6

def fourPointOddPart (positions : FourPointConfiguration) : ℂ × ℂ :=
  ((positions 0 - positions 1) / 2, (positions 2 - positions 3) / 2)

theorem fourPointOddPart_sub (first second : FourPointConfiguration) :
    fourPointOddPart (first - second) = fourPointOddPart first - fourPointOddPart second := by
  ext <;> simp [fourPointOddPart] <;> ring

theorem fourPointOddPart_constant (center : ℂ) :
    fourPointOddPart (fun _ => center) = 0 := by
  simp [fourPointOddPart]

theorem fourPointOddPart_norm_le (positions : FourPointConfiguration) :
    ‖fourPointOddPart positions‖ ≤ ‖positions‖ := by
  apply max_le
  all_goals
    simp only [fourPointOddPart, Prod.fst, Prod.snd, norm_div, Complex.norm_ofNat]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    first
    | exact (norm_sub_le _ _).trans (by
        have first := norm_le_pi_norm positions 0
        have second := norm_le_pi_norm positions 1
        linarith)
    | exact (norm_sub_le _ _).trans (by
        have first := norm_le_pi_norm positions 2
        have second := norm_le_pi_norm positions 3
        linarith)

theorem fourPointOddPart_linearization_pairCenter (coefficient : ℝ)
    (positive negative firstCenter secondCenter : ℂ) :
    fourPointOddPart (fourPointLinearization coefficient (centrallySymmetricFourPoint positive negative)
      (fourPointPairCenterMode firstCenter secondCenter)) = 0 := by
  rw [fourPointLinearization_pairCenterMode, fourPointOddPart_constant]

theorem fourPointPairCenterMode_balanced_norm (center : ℂ) :
    ‖fourPointPairCenterMode center (-center)‖ = ‖center‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg center)).mpr
    intro target
    fin_cases target <;> simp [fourPointPairCenterMode]
  · simpa [fourPointPairCenterMode] using
      norm_le_pi_norm (fourPointPairCenterMode center (-center)) 0

theorem fourPointField_pairCenter_translation (coefficient : ℝ)
    (positive negative firstCenter secondCenter : ℂ) :
    fourPointField coefficient
        (centrallySymmetricFourPoint positive negative + fourPointPairCenterMode firstCenter secondCenter) =
      fourPointField coefficient
        (centrallySymmetricFourPoint positive negative +
          fourPointPairCenterMode ((firstCenter - secondCenter) / 2) (-((firstCenter - secondCenter) / 2))) := by
  have identity : centrallySymmetricFourPoint positive negative + fourPointPairCenterMode firstCenter secondCenter =
      (centrallySymmetricFourPoint positive negative +
        fourPointPairCenterMode ((firstCenter - secondCenter) / 2) (-((firstCenter - secondCenter) / 2))) +
        fun _ => (firstCenter + secondCenter) / 2 := by
    funext target
    fin_cases target <;> simp [centrallySymmetricFourPoint, fourPointPairCenterMode] <;> ring
  rw [identity, fourPointField_translation_invariant]

theorem fourPointField_uniform_pairCenter_remainder {base : FourPointConfiguration}
    (noncollision : FourPointNoncollision base) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ positive negative firstCenter secondCenter : ℂ,
      FourPointNoncollision (centrallySymmetricFourPoint positive negative) →
      ‖centrallySymmetricFourPoint positive negative - base‖ < radius →
      ‖fourPointPairCenterMode firstCenter secondCenter‖ < radius →
      ‖fourPointOddPart (fourPointField coefficient
          (centrallySymmetricFourPoint positive negative + fourPointPairCenterMode firstCenter secondCenter)) -
        fourPointOddPart (fourPointField coefficient (centrallySymmetricFourPoint positive negative))‖ ≤
        bound * |coefficient| * ‖fourPointPairCenterMode firstCenter secondCenter‖ ^ 2 := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointField_uniform_quadratic_remainder noncollision
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient positive negative firstCenter secondCenter centerNoncollision centerSmall incrementSmall
  have control := estimate coefficient (centrallySymmetricFourPoint positive negative)
    (fourPointPairCenterMode firstCenter secondCenter) centerNoncollision centerSmall incrementSmall
  have projected := (fourPointOddPart_norm_le
    (fourPointField coefficient (centrallySymmetricFourPoint positive negative +
        fourPointPairCenterMode firstCenter secondCenter) -
      fourPointField coefficient (centrallySymmetricFourPoint positive negative) -
      fourPointLinearization coefficient (centrallySymmetricFourPoint positive negative)
        (fourPointPairCenterMode firstCenter secondCenter))).trans control
  simpa only [fourPointOddPart_sub, fourPointOddPart_linearization_pairCenter, sub_zero] using projected

theorem fourPointField_uniform_centerDifference_remainder {base : FourPointConfiguration}
    (noncollision : FourPointNoncollision base) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ positive negative firstCenter secondCenter : ℂ,
      FourPointNoncollision (centrallySymmetricFourPoint positive negative) →
      ‖centrallySymmetricFourPoint positive negative - base‖ < radius →
      ‖firstCenter - secondCenter‖ < 2 * radius →
      ‖fourPointOddPart (fourPointField coefficient
          (centrallySymmetricFourPoint positive negative + fourPointPairCenterMode firstCenter secondCenter)) -
        fourPointOddPart (fourPointField coefficient (centrallySymmetricFourPoint positive negative))‖ ≤
        bound * |coefficient| * ‖firstCenter - secondCenter‖ ^ 2 / 4 := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointField_uniform_pairCenter_remainder noncollision
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient positive negative firstCenter secondCenter centerNoncollision centerSmall differenceSmall
  rw [fourPointField_pairCenter_translation]
  have balancedSmall : ‖fourPointPairCenterMode ((firstCenter - secondCenter) / 2)
      (-((firstCenter - secondCenter) / 2))‖ < radius := by
    rw [fourPointPairCenterMode_balanced_norm, norm_div, Complex.norm_ofNat]
    linarith
  have control := estimate coefficient positive negative ((firstCenter - secondCenter) / 2)
    (-((firstCenter - secondCenter) / 2)) centerNoncollision centerSmall balancedSmall
  rw [fourPointPairCenterMode_balanced_norm, norm_div, Complex.norm_ofNat] at control
  convert control using 1 <;> ring

theorem fourPointSignedMoment_centerDifference (positions : FourPointConfiguration) :
    fourPointSignedMoment positions =
      2 * ((positions 0 + positions 1) / 2 - (positions 2 + positions 3) / 2) := by
  simp [fourPointSignedMoment, fourPointSign, Fin.sum_univ_succ]
  ring

theorem fourPointField_uniform_signedMoment_remainder {base : FourPointConfiguration}
    (noncollision : FourPointNoncollision base) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ positions : FourPointConfiguration,
      FourPointNoncollision (centrallySymmetricFourPoint (fourPointOddPart positions).1
        (fourPointOddPart positions).2) →
      ‖centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2 - base‖ < radius →
      ‖fourPointSignedMoment positions‖ < 4 * radius →
      ‖fourPointOddPart (fourPointField coefficient positions) -
        fourPointOddPart (fourPointField coefficient
          (centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2))‖ ≤
        bound * |coefficient| * ‖fourPointSignedMoment positions‖ ^ 2 / 16 := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointField_uniform_centerDifference_remainder noncollision
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient positions centerNoncollision centerSmall momentSmall
  have momentNorm : ‖fourPointSignedMoment positions‖ =
      2 * ‖(positions 0 + positions 1) / 2 - (positions 2 + positions 3) / 2‖ := by
    rw [fourPointSignedMoment_centerDifference, norm_mul, Complex.norm_ofNat]
  have differenceSmall : ‖(positions 0 + positions 1) / 2 - (positions 2 + positions 3) / 2‖ <
      2 * radius := by rw [momentNorm] at momentSmall; linarith
  have control := estimate coefficient (fourPointOddPart positions).1 (fourPointOddPart positions).2
    ((positions 0 + positions 1) / 2) ((positions 2 + positions 3) / 2)
    centerNoncollision centerSmall differenceSmall
  have decomposition : centrallySymmetricFourPoint (fourPointOddPart positions).1
      (fourPointOddPart positions).2 + fourPointPairCenterMode ((positions 0 + positions 1) / 2)
        ((positions 2 + positions 3) / 2) = positions :=
    (fourPoint_increment_decomposition positions).symm
  rw [decomposition] at control
  rw [momentNorm]
  convert control using 1 <;> ring

theorem fourPointSignedMoment_conserved {trajectory : ℝ → FourPointConfiguration} {coefficient : ℝ}
    (equation : ∀ time target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target) time) (firstTime secondTime : ℝ) :
    fourPointSignedMoment (trajectory firstTime) = fourPointSignedMoment (trajectory secondTime) := by
  have derivative := fun time => fourPointSignedMoment_hasDerivAt (equation time)
  exact is_const_of_deriv_eq_zero (fun time => (derivative time).differentiableAt)
    (fun time => (derivative time).deriv) firstTime secondTime

theorem fourPointOddPart_forced_hasDerivAt {trajectory : ℝ → FourPointConfiguration}
    {coefficient time : ℝ} {forcing : FourPointConfiguration}
    (equation : ∀ target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target + forcing target) time) :
    HasDerivAt (fun current => fourPointOddPart (trajectory current))
      (fourPointOddPart (fourPointField coefficient (trajectory time)) + fourPointOddPart forcing) time := by
  have derivative := (((equation 0).sub (equation 1)).div_const 2).prodMk
    (((equation 2).sub (equation 3)).div_const 2)
  convert derivative using 1
  ext <;> simp [fourPointOddPart] <;> ring

theorem fourPointField_zero_signedMoment (coefficient : ℝ) {positions : FourPointConfiguration}
    (zeroMoment : fourPointSignedMoment positions = 0) :
    fourPointField coefficient positions =
      fourPointField coefficient
        (centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2) := by
  have centersEqual : (positions 0 + positions 1) / 2 = (positions 2 + positions 3) / 2 := by
    rw [fourPointSignedMoment_centerDifference] at zeroMoment
    linear_combination (1 / 2 : ℂ) * zeroMoment
  have decomposition : positions =
      centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2 +
        fun _ => (positions 0 + positions 1) / 2 := by
    calc
      positions = centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2 +
          fourPointPairCenterMode ((positions 0 + positions 1) / 2) ((positions 2 + positions 3) / 2) :=
        fourPoint_increment_decomposition positions
      _ = _ := by
        congr 1
        funext target
        fin_cases target <;> simp [fourPointPairCenterMode, ← centersEqual]
  exact (congrArg (fourPointField coefficient) decomposition).trans
    (fourPointField_translation_invariant coefficient _ _)

end EulerNonuniqueness.Section6
