import EulerNonuniqueness.General.Brouwer.FixedPoint

noncomputable section

open Set Metric

theorem no_continuous_ball_boundary_retraction
    {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space] [FiniteDimensional ℝ space]
    {radius : ℝ} (radiusPositive : 0 < radius)
    {retraction : closedBall (0 : space) radius → space}
    (continuous : Continuous retraction)
    (imageSphere : ∀ position, ‖retraction position‖ = radius)
    (boundaryIdentity : ∀ position : closedBall (0 : space) radius,
      ‖(position : space)‖ = radius → retraction position = position) : False := by
  have mapsInto : ∀ position, -retraction position ∈ closedBall (0 : space) radius := by
    intro position
    rw [mem_closedBall, dist_zero_right, norm_neg, imageSphere]
  let selfMap : C(closedBall (0 : space) radius, closedBall (0 : space) radius) :=
    ⟨fun position => ⟨-retraction position, mapsInto position⟩, continuous.neg.subtype_mk mapsInto⟩
  obtain ⟨fixed, fixedIdentity⟩ := EulerNonuniqueness.General.Brouwer.brouwer_fixed_point
    (closedBall (0 : space) radius) (convex_closedBall _ _) (isCompact_closedBall _ _)
    ⟨0, mem_closedBall_self radiusPositive.le⟩ selfMap
  have identity : -retraction fixed = (fixed : space) := congrArg Subtype.val fixedIdentity
  have fixedOnSphere : ‖(fixed : space)‖ = radius := by
    rw [← identity, norm_neg, imageSphere]
  rw [boundaryIdentity fixed fixedOnSphere] at identity
  have sumZero : (fixed : space) + fixed = 0 := by
    calc
      (fixed : space) + fixed = -fixed + fixed := congrArg (fun value : space => value + fixed) identity.symm
      _ = 0 := neg_add_cancel _
  have twiceZero : (2 : ℝ) • (fixed : space) = 0 := by simpa only [two_smul] using sumZero
  have fixedZero : (fixed : space) = 0 := (smul_eq_zero.mp twiceZero).resolve_left (by norm_num)
  rw [fixedZero, norm_zero] at fixedOnSphere
  linarith

theorem no_continuous_closedBall_retraction_to_sphere
    {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space] [FiniteDimensional ℝ space]
    {radius : ℝ} (radiusPositive : 0 < radius) {retraction : space → space}
    (continuous : ContinuousOn retraction (closedBall 0 radius))
    (imageSphere : ∀ position ∈ closedBall 0 radius, ‖retraction position‖ = radius)
    (boundaryIdentity : ∀ position, ‖position‖ = radius → retraction position = position) : False := by
  let selfMap : C(closedBall (0 : space) radius, closedBall (0 : space) radius) :=
    ⟨fun position => ⟨-retraction position, by
      rw [mem_closedBall, dist_zero_right, norm_neg, imageSphere position position.property]⟩,
      ((continuousOn_iff_continuous_restrict.mp continuous).neg).subtype_mk (fun position => by
        rw [mem_closedBall, dist_zero_right, norm_neg]
        change ‖retraction (position : space)‖ ≤ radius
        exact (imageSphere position position.property).le)⟩
  obtain ⟨fixed, fixedIdentity⟩ := EulerNonuniqueness.General.Brouwer.brouwer_fixed_point
    (closedBall (0 : space) radius) (convex_closedBall _ _) (isCompact_closedBall _ _)
    ⟨0, mem_closedBall_self radiusPositive.le⟩ selfMap
  have identity : -retraction fixed = (fixed : space) := congrArg Subtype.val fixedIdentity
  have fixedOnSphere : ‖(fixed : space)‖ = radius := by
    rw [← identity, norm_neg]
    exact imageSphere fixed fixed.property
  rw [boundaryIdentity fixed fixedOnSphere] at identity
  have fixedZero : (fixed : space) = 0 := by
    have sumZero : (fixed : space) + fixed = 0 := by
      calc
        (fixed : space) + fixed = -fixed + fixed := congrArg (fun value : space => value + fixed) identity.symm
        _ = 0 := neg_add_cancel _
    have twiceZero : (2 : ℝ) • (fixed : space) = 0 := by simpa only [two_smul] using sumZero
    exact (smul_eq_zero.mp twiceZero).resolve_left (by norm_num)
  rw [fixedZero, norm_zero] at fixedOnSphere
  linarith
