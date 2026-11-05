import EulerNonuniqueness.Section3.CompactParameterDifferentiation

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

theorem hasDerivAt_nested_intervalIntegral_of_joint_continuous
    (function variation : ℝ → ℝ → ℝ → ℝ)
    (function_continuous : Continuous (fun triple : (ℝ × ℝ) × ℝ => function triple.1.1 triple.1.2 triple.2))
    (variation_continuous : Continuous (fun triple : (ℝ × ℝ) × ℝ => variation triple.1.1 triple.1.2 triple.2))
    (time radius lower upper inner_lower inner_upper : ℝ) (radius_positive : 0 < radius)
    (derivative : ∀ parameter ∈ Metric.ball time radius, ∀ label ∈ uIcc lower upper,
      ∀ scale ∈ uIcc inner_lower inner_upper,
      HasDerivAt (fun parameter => function parameter label scale) (variation parameter label scale) parameter) :
    HasDerivAt (fun parameter => ∫ label in lower..upper,
      ∫ scale in inner_lower..inner_upper, function parameter label scale)
      (∫ label in lower..upper, ∫ scale in inner_lower..inner_upper, variation time label scale) time := by
  have inner_continuous : Continuous (fun pair : ℝ × ℝ =>
      ∫ scale in inner_lower..inner_upper, function pair.1 pair.2 scale) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
      function_continuous continuous_const
  have inner_variation_continuous : Continuous (fun pair : ℝ × ℝ =>
      ∫ scale in inner_lower..inner_upper, variation pair.1 pair.2 scale) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
      variation_continuous continuous_const
  apply hasDerivAt_intervalIntegral_of_joint_continuous
    (fun parameter label => ∫ scale in inner_lower..inner_upper, function parameter label scale)
    (fun parameter label => ∫ scale in inner_lower..inner_upper, variation parameter label scale)
    time lower upper (radius / 2) (by positivity) inner_continuous inner_variation_continuous
  intro label label_member parameter parameter_member
  apply hasDerivAt_intervalIntegral_of_joint_continuous
    (fun parameter scale => function parameter label scale)
    (fun parameter scale => variation parameter label scale)
    parameter inner_lower inner_upper (radius / 2) (by positivity)
  · exact function_continuous.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)
  · exact variation_continuous.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)
  · intro scale scale_member current current_member
    have current_inside : current ∈ Metric.ball time radius := by
      have triangle := dist_triangle current parameter time
      have first : dist current parameter < radius / 2 := current_member
      have second : dist parameter time < radius / 2 := parameter_member
      change dist current time < radius
      linarith
    exact derivative current current_inside label label_member scale scale_member

end

end EulerNonuniqueness.Paper
