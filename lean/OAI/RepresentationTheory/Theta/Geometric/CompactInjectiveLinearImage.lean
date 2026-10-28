import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.InjectiveAnalyticImage

/-! # Compact Injective Linear Image -/

namespace OAI.RepresentationTheory.Theta.Geometric.CompactInjectiveLinearImage

noncomputable section

/-! Local equations of a compact set transport under an injective linear map. -/

open Set
open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.InjectiveAnalyticImage.Constructions.Cone

theorem compact_injective_linear_image_local
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {S : Set E} (hS : IsCompact S)
    (L : E →L[ℂ] F) (hL : Function.Injective L) (y : F)
    (hlocal : ∀ x ∈ S, L x = y → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S x) :
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (L '' S) y := by
  obtain ⟨R, hR⟩ := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.InjectiveAnalyticImage.Constructions.Cone.exists_continuousLinear_leftInverse L hL
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
    exact (hS.isClosed.preimage R.continuous).inter
      (isClosed_eq ((L.continuous.comp R.continuous).sub continuous_id) continuous_const)
  by_cases hy : y ∈ L '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    have hRx : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (R (L x)) := by
      rw [hR]
      exact hlocal x hx rfl
    have hpre := hRx.preimage isOpen_univ (mem_univ (L x)) R.differentiable.differentiableOn
    have hzero := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticSetOperations.Constructions.Cone.holomorphicZeroSetAt_zero_fiber isOpen_univ
      ((L.differentiable.comp R.differentiable).sub differentiable_id).differentiableOn
      (mem_univ (L x))
    rw [himage]
    exact hpre.inter hzero
  · exact AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticSetOperations.Constructions.Cone.holomorphicZeroSetAt_of_not_mem_closed hclosed hy

end

end OAI.RepresentationTheory.Theta.Geometric.CompactInjectiveLinearImage
