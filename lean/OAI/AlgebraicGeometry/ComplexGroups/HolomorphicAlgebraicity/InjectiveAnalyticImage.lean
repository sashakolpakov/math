import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticSetOperations
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearRankCoordinates

/-! # Injective Analytic Image -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.InjectiveAnalyticImage.Constructions.Cone

noncomputable section

/-!
# Local analytic equations under injective complex linear maps
-/

open Set

theorem exists_continuousLinear_leftInverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (L : E →L[ℂ] F) (hL : Function.Injective L) :
    ∃ R : F →L[ℂ] E, ∀ x, R (L x) = x := by
  obtain ⟨π, _, _, hπ, _⟩ := LinearRankCoordinates.Constructions.FiniteRank.exists_rank_coordinates L
  have hbij : Function.Bijective L.toLinearMap.rangeRestrict :=
    ⟨fun x y h => hL (congrArg Subtype.val h), LinearMap.range_eq_top.mp L.toLinearMap.range_rangeRestrict⟩
  let e := (LinearEquiv.ofBijective L.toLinearMap.rangeRestrict hbij).toContinuousLinearEquiv
  refine ⟨e.symm.toContinuousLinearMap.comp π, ?_⟩
  intro x
  change e.symm (π (L x)) = x
  rw [hπ ⟨L x, ⟨x, rfl⟩⟩]
  exact e.symm_apply_apply x

theorem holomorphicZeroSetAt_injective_linear_image
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {S : Set E} (hS : IsClosed S)
    (hlocal : ∀ x ∈ S, x ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S x)
    (L : E →L[ℂ] F) (hL : Function.Injective L) (y : F) (hy0 : y ≠ 0) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (L '' S) y := by
  obtain ⟨R, hR⟩ := exists_continuousLinear_leftInverse L hL
  have himage : L '' S = R ⁻¹' S ∩ {z | L (R z) - z = 0} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      constructor
      · change R (L x) ∈ S
        simpa only [hR] using hx
      · change L (R (L x)) - L x = 0
        rw [hR, sub_self]
    · rintro ⟨hzS, hz⟩
      exact ⟨R z, hzS, sub_eq_zero.mp hz⟩
  have hclosed : IsClosed (L '' S) := by
    rw [himage]
    exact (hS.preimage R.continuous).inter
      (isClosed_eq ((L.continuous.comp R.continuous).sub continuous_id) continuous_const)
  by_cases hy : y ∈ L '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    have hx0 : x ≠ 0 := by
      intro hz
      exact hy0 (by rw [hz, map_zero])
    have hRx : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (R (L x)) := by
      rw [hR]
      exact hlocal x hx hx0
    have hpre := hRx.preimage isOpen_univ (mem_univ (L x)) R.differentiable.differentiableOn
    have hzero := AnalyticSetOperations.Constructions.Cone.holomorphicZeroSetAt_zero_fiber isOpen_univ
      ((L.differentiable.comp R.differentiable).sub differentiable_id).differentiableOn
      (mem_univ (L x))
    rw [himage]
    exact hpre.inter hzero
  · exact AnalyticSetOperations.Constructions.Cone.holomorphicZeroSetAt_of_not_mem_closed hclosed hy

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.InjectiveAnalyticImage.Constructions.Cone
