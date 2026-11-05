import EulerNonuniqueness.Section6.PointScaling

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

def physicalSeparatingPointOrbit (orbit : SeparatingOrbit) (frequency length : ℝ)
    (direction center : ℂ) (timeShift time : ℝ) : FourPointConfiguration :=
  fun target => center + (length : ℂ) * direction *
    centrallySymmetricFourPoint (orbit.positive (frequency * time + timeShift))
      (-orbit.negative (frequency * time + timeShift)) target

theorem physicalSeparatingPointOrbit_actual_equation (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) (frequency length : ℝ) (direction center : ℂ)
    (timeShift time : ℝ) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1) :
    HasDerivAt (physicalSeparatingPointOrbit orbit frequency length direction center timeShift)
      (fourPointField (frequency * length ^ 2)
        (physicalSeparatingPointOrbit orbit frequency length direction center timeShift time)) time ∧
      FourPointNoncollision (physicalSeparatingPointOrbit orbit frequency length direction center timeShift time) := by
  let reference := fun current => centrallySymmetricFourPoint (orbit.positive current) (-orbit.negative current)
  have properties := normalizedSeparatingOrbit_full_point_equation orbit normalized (frequency * time + timeShift)
  have positionIdentity : physicalSeparatingPointOrbit orbit frequency length direction center timeShift time =
      ((fun target => (length : ℂ) * direction * reference (frequency * time + timeShift) target) + fun _ => center) := by
    funext target
    dsimp [physicalSeparatingPointOrbit, reference]
    ring
  have fieldIdentity : fourPointField (frequency * length ^ 2)
      (physicalSeparatingPointOrbit orbit frequency length direction center timeShift time) =
      fun target => ((frequency * length : ℝ) : ℂ) * direction *
        fourPointField 1 (reference (frequency * time + timeShift)) target := by
    calc
      _ = fourPointField (frequency * length ^ 2)
          ((fun target => (length : ℂ) * direction * reference (frequency * time + timeShift) target) + fun _ => center) := by
        rw [positionIdentity]
      _ = fourPointField (frequency * length ^ 2)
          (fun target => (length : ℂ) * direction * reference (frequency * time + timeShift) target) :=
        fourPointField_translation_invariant _ _ _
      _ = _ := fourPointField_physical_dilation frequency length lengthPositive directionNorm _
  constructor
  · rw [fieldIdentity]
    apply hasDerivAt_pi.mpr
    intro target
    have affine := ((hasDerivAt_id time).const_mul frequency).add_const timeShift
    have derivative := (((hasDerivAt_pi.mp properties.1 target).scomp time affine).const_mul
      ((length : ℂ) * direction)).const_add center
    convert derivative using 1
    simp only [Complex.real_smul]
    push_cast
    dsimp [reference]
    ring
  · have directionNonzero : direction ≠ 0 := norm_ne_zero_iff.mp (by rw [directionNorm]; norm_num)
    have scaleNonzero : (length : ℂ) * direction ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr lengthPositive.ne') directionNonzero
    intro target source different
    have identity : physicalSeparatingPointOrbit orbit frequency length direction center timeShift time target -
        physicalSeparatingPointOrbit orbit frequency length direction center timeShift time source =
        ((length : ℂ) * direction) *
          (reference (frequency * time + timeShift) target - reference (frequency * time + timeShift) source) := by
      dsimp [physicalSeparatingPointOrbit, reference]
      ring
    rw [identity]
    exact mul_ne_zero scaleNonzero (properties.2 target source different)

end EulerNonuniqueness.Section6
