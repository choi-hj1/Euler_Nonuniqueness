import EulerNonuniqueness.Section4.ReferenceForeignStrainGeometry
import EulerNonuniqueness.Section4.ReferenceCenterDefectScale
import EulerNonuniqueness.Section4.ReferenceNeutralMoment
import EulerNonuniqueness.Section3.HolderPaperBoundaryBound

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_reference_foreign_strain_bounds
    (amplitude bound : ℝ) (amplitudePositive : 0 < amplitude) (boundNonnegative : 0 ≤ bound) :
    ∃ constant ≥ (1 : ℝ),
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales),
      scales.amplitude = amplitude →
      (∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
      (∀ (index : Fin count) (patch : Fin 4),
        (family.patch (finProdFinEquiv (index, patch))).radius = scales.radius (index.val + 1)) →
      ∀ {horizon finish threshold : ℝ},
      ∀ (evolution : FinitePatchEvolution scales family.patchMotion horizon),
      0 < horizon → 0 ≤ finish → finish ≤ 2 → Icc 0 finish ⊆ Icc 0 horizon →
      1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {phase unstable : Fin count → ℝ},
      ReferenceInitialDisks scales family.patchMotion phase unstable threshold →
      (∀ time ∈ Icc 0 finish, ∀ source,
        time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
      (∀ time ∈ Icc 0 finish, ∀ source label, (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label)) →
      (∀ time ∈ Icc 0 finish, ∀ index : Fin count,
        scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index) →
      (∀ time ∈ Icc 0 finish, ∀ index : Fin count,
        diagonalDifference family.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 finish, ∀ index, |radialShape family.patchMotion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 finish, ∀ index,
        ‖centroidAsymmetry family.patchMotion time index‖ ≤ scales.length (index.val + 1) / 64) →
      (∀ time ∈ Icc 0 finish, ∀ receiver source : Fin count, receiver ≠ source →
        |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
          ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖) →
      (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
      (∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000) →
      (∀ index : Fin count,
        scales.omega (index.val + 1) * scales.length (index.val + 1) ≤ scales.location (index.val + 1)) →
      (∀ index : Fin count, scales.omega (index.val + 1) ^ 4 * scales.length (index.val + 1) ≤ 1) →
      ∀ (deformation : ℝ → Fin count → ℝ),
      (∀ time ∈ Icc 0 finish, ∀ index patch,
        BoundaryCloseToCircle scales family.patchMotion time index patch (deformation time index)) →
      (∀ time ∈ Icc 0 finish, ∀ index, 0 ≤ deformation time index) →
      (∀ time ∈ Icc 0 finish, ∀ index, deformation time index ≤ 1 / 16) →
      (∀ time ∈ Icc 0 finish, ∀ index,
        deformation time index ≤ bound / scales.omega (index.val + 1) ^ 2) →
      scales.strain ≤ 1 → scales.hessian ≤ 1 →
      ∀ time ∈ Icc 0 finish, ∀ index : Fin count,
        HasDerivAt (family.foreignQuadrupoleStrain index)
          (family.foreignQuadrupoleStrainDerivative scales index time) time ∧
        ‖family.foreignQuadrupoleStrain index time‖ ≤ constant * scales.strain ∧
        ‖family.foreignQuadrupoleStrainDerivative scales index time‖ ≤
          constant * (scales.strain ^ 2 + 1 / scales.omega (index.val + 1) ^ 4) := by
  let memory := (995328 / Real.pi) * Real.exp (2304 / Real.pi)
  let residual := (13824000000 + 113246208 / Real.pi) * bound / amplitude
  let defect := 40000 * memory + 497664 / Real.pi + residual
  let first := (55296 / Real.pi) * defect
  let second := 34504704 / Real.pi ^ 2
  let constant := 1 + 1152 / Real.pi + first + second
  have memoryNonnegative : 0 ≤ memory := by dsimp only [memory]; positivity
  have residualNonnegative : 0 ≤ residual := by dsimp only [residual]; positivity
  have defectNonnegative : 0 ≤ defect := by dsimp only [defect]; positivity
  have firstNonnegative : 0 ≤ first := by dsimp only [first]; positivity
  have secondNonnegative : 0 ≤ second := by dsimp only [second]; positivity
  have sizeNonnegative : (0 : ℝ) ≤ 1152 / Real.pi := by positivity
  refine ⟨constant, by dsimp only [constant]; linarith, ?_⟩
  intro count family scales amplitudeEquation densityEquation radiusEquation horizon finish threshold evolution horizonPositive
    finishNonnegative finishBound timeRange frequencyBound ratioBound alphaPositive phase unstable initial inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation lengthSmall radiusSmall transportSmall
    polynomialSmall deformation control nonnegative small deformationBound strainBound hessianBound
  have actualAmplitudePositive : 0 < scales.amplitude := amplitudeEquation.symm ▸ amplitudePositive
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (scales.location_pos _).le _)
  have commonControl (time : ℝ) (member : time ∈ Icc 0 finish) (index : Fin count) (patch : Fin 4) :
      BoundaryCloseToCircle scales family.patchMotion time index patch (1 / 16) := by
    obtain ⟨relabeling, periodic, relabelingBound, errorBound⟩ := control time member index patch
    exact ⟨relabeling, periodic, relabelingBound, errorBound.mono (small time member index)⟩
  have radiusWeaker (index : Fin count) : scales.radius (index.val + 1) * (1 + (1 : ℝ) / 16) ≤
      scales.length (index.val + 1) / 32 := by
    linarith only [radiusSmall index, scales.length_pos (index.val + 1)]
  have neutral (index : Fin count) := family.reference_centroidAsymmetry_bound scales densityEquation evolution
    horizonPositive finishNonnegative timeRange actualAmplitudePositive frequencyBound ratioBound alphaPositive initial
    inside material differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation lengthSmall commonControl
    radiusWeaker index
  intro time member index
  have omegaBound : 1 ≤ scales.omega (index.val + 1) := frequencyBound.trans
    (scales.omega_ge_frequency frequencyPositive (by linarith) _)
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have locationPositive := scales.location_pos (index.val + 1)
  have lengthPositive := scales.length_pos (index.val + 1)
  have lengthBound : scales.length (index.val + 1) ≤ 1 := by
    have powerOne : 1 ≤ scales.omega (index.val + 1) ^ 4 := one_le_pow₀ omegaBound
    nlinarith [polynomialSmall index]
  have geometry := evolution.reference_centroid_field_geometry (timeRange member) actualAmplitudePositive frequencyPositive
    ratioPositive (differenceLower time member) (differenceUpper time member) (radialSmall time member)
    (asymmetrySmall time member) (centerSeparation time member) lengthSmall radiusSmall (deformation time)
    (control time member) (nonnegative time member) (small time member) index
  have momentBound : ‖centroidAsymmetry family.patchMotion time index‖ ≤
      memory * scales.hessian * scales.length (index.val + 1) ^ 2 := by
    have timeNonnegative := member.1
    have timeBound : time ≤ 2 := member.2.trans finishBound
    have exponentBound : (1152 / Real.pi) * scales.strain * time ≤ 2304 / Real.pi := by
      calc
        _ ≤ (1152 / Real.pi) * 1 * 2 := by gcongr
        _ = _ := by ring
    apply (neutral index time member).trans
    calc
      _ ≤ (497664 / Real.pi) * scales.hessian * scales.length (index.val + 1) ^ 2 * 2 *
          Real.exp (2304 / Real.pi) := by gcongr
      _ = _ := by dsimp only [memory]; ring
  have velocityBound := family.reference_refined_center_velocity_bound scales evolution (timeRange member) actualAmplitudePositive
    frequencyBound ratioBound alphaPositive index (fun patch => inside time member _) (fun patch label => by
      rw [family.patchVorticity_eq scales densityEquation]
      exact material time member _ label) (control time member index) (nonnegative time member index)
    (small time member index) boundNonnegative (deformationBound time member index) lengthBound hessianBound geometry
  have scalarBound := reference_center_defect_scale_bound omegaBound lengthPositive locationPositive hessianNonnegative
    hessianBound memoryNonnegative residualNonnegative momentBound (transportSmall index) (polynomialSmall index)
  rw [amplitudeEquation] at velocityBound
  have relativeBound :
      ‖deriv (fun current => quadrupoleCenter family.patchMotion current index) time -
          biotSavart (externalPatchVorticity scales family.patchMotion time index)
            (quadrupoleCenter family.patchMotion time index)‖ / scales.location (index.val + 1) ≤
        defect / scales.omega (index.val + 1) ^ 4 :=
    (div_le_div_of_nonneg_right velocityBound locationPositive.le).trans scalarBound
  have receiverBounded := family.reference_receiver_domain_bound scales evolution (timeRange member) index
    (scales.radius_pos actualAmplitudePositive frequencyPositive ratioPositive _) (radiusSmall index)
    (control time member index) (small time member index) geometry
  have receiverSmall : 2 * (4 * scales.length (index.val + 1)) ≤ scales.location (index.val + 1) / 24 := by
    linarith [lengthSmall index]
  have temporal := family.norm_foreignQuadrupoleStrainDerivative_le scales evolution (timeRange member) densityEquation
    actualAmplitudePositive frequencyBound ratioBound alphaPositive index receiverBounded receiverSmall geometry.centerSeparated
  refine ⟨family.foreignQuadrupoleStrain_hasDerivAt scales index densityEquation (inside time member)
    (fun source _ => material time member source) (div_pos locationPositive (by norm_num))
    (family.reference_foreign_source_center_gaps scales radiusEquation lengthSmall radiusSmall index geometry), ?_, ?_⟩
  · apply (family.norm_reference_foreign_strain_le scales evolution (timeRange member) densityEquation actualAmplitudePositive
      frequencyBound ratioBound alphaPositive index geometry).trans
    apply mul_le_mul_of_nonneg_right _ strainNonnegative
    dsimp only [constant]
    linarith
  · have scaled := mul_le_mul_of_nonneg_left relativeBound
      (by positivity : 0 ≤ (55296 / Real.pi) * scales.strain)
    have mixed : scales.strain / scales.omega (index.val + 1) ^ 4 ≤ 1 / scales.omega (index.val + 1) ^ 4 :=
      div_le_div_of_nonneg_right strainBound (pow_nonneg omegaPositive.le _)
    have estimate : ‖family.foreignQuadrupoleStrainDerivative scales index time‖ ≤
        first / scales.omega (index.val + 1) ^ 4 + second * scales.strain ^ 2 := by
      calc
        _ ≤ (55296 / Real.pi) * scales.strain * (defect / scales.omega (index.val + 1) ^ 4) +
            second * scales.strain ^ 2 := temporal.trans (by convert add_le_add_right scaled (second * scales.strain ^ 2) using 1 <;> ring)
        _ = first * (scales.strain / scales.omega (index.val + 1) ^ 4) + second * scales.strain ^ 2 := by
          dsimp only [first]; ring
        _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul] using
          add_le_add_right (mul_le_mul_of_nonneg_left mixed firstNonnegative) (second * scales.strain ^ 2)
    apply estimate.trans
    have firstBound : first ≤ constant := by dsimp only [constant]; linarith
    have secondBound : second ≤ constant := by dsimp only [constant]; linarith
    have combined := add_le_add (div_le_div_of_nonneg_right firstBound (pow_nonneg omegaPositive.le 4))
      (mul_le_mul_of_nonneg_right secondBound (sq_nonneg scales.strain))
    exact combined.trans_eq (by ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
