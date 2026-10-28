import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.TangentBaseChange

/-! # Tangent Open Restriction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.TangentOpenRestriction

noncomputable section

/-! Actual relative tangent points are unchanged when source and
base are restricted to open neighborhoods of their prescribed point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace RelativeTangent

theorem map_bijective_of_open
    {C : CommRingCat.{0}} [IsLocalRing C] (J : Ideal C) (hJ : J ^ 2 = ⊥)
    {X Y X' Y' : Scheme.{0}} (p : Y ⟶ X) (g : Spec C ⟶ Y)
    (p' : Y' ⟶ X') (g' : Spec C ⟶ Y') (f : Y ⟶ Y') [IsOpenImmersion f]
    (a : X ⟶ X') [Mono a] (hf : f ≫ p' = p ≫ a) (hg : g ≫ f = g') :
    Function.Bijective (TangentBaseChange.RelativeTangent.map J hJ p g p' g' f a hf hg) := by
  constructor
  · intro v w h
    apply TangentBaseChange.RelativeTangent.point_injective J hJ p g
    apply (cancel_mono f).mp
    exact (TangentBaseChange.RelativeTangent.point_map J hJ p g p' g' f a hf hg v).symm.trans
      ((congrArg (TangentBaseChange.RelativeTangent.point J hJ p' g') h).trans (TangentBaseChange.RelativeTangent.point_map J hJ p g p' g' f a hf hg w))
  · intro w
    let z := TangentBaseChange.RelativeTangent.point J hJ p' g' w
    have hclosed : z (IsLocalRing.closedPoint C) ∈ f.opensRange := by
      have hz : z (IsLocalRing.closedPoint C) = g' (IsLocalRing.closedPoint C) :=
        AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.toPoint_closedPoint J hJ (Scheme.stalkClosedPointTo g') w.val
      exact ⟨g (IsLocalRing.closedPoint C), (congrArg (fun q => q (IsLocalRing.closedPoint C)) hg).trans hz.symm⟩
    have htop : z ⁻¹ᵁ f.opensRange = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem z hclosed
    have hrange : Set.range z ⊆ Set.range f := by
      rintro _ ⟨y, rfl⟩
      have hy : y ∈ z ⁻¹ᵁ f.opensRange := htop.symm ▸ (show y ∈ (⊤ : (Spec C).Opens) from trivial)
      exact hy
    let l := IsOpenImmersion.lift f z hrange
    have hl : l ≫ f = z := IsOpenImmersion.lift_fac f z hrange
    have hr : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ l =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g := by
      apply (cancel_mono f).mp
      rw [Category.assoc, hl, Category.assoc, hg]
      exact TangentBaseChange.RelativeTangent.point_reduction J hJ p' g' w
    have hb : l ≫ p = g ≫ p := by
      apply (cancel_mono a).mp
      rw [Category.assoc, ← hf, ← Category.assoc, hl]
      exact (TangentBaseChange.RelativeTangent.point_over J hJ p' g' w).trans
        ((congrArg (fun q => q ≫ p') hg).symm.trans (by rw [Category.assoc, hf, ← Category.assoc]))
    obtain ⟨v, hv⟩ := TangentBaseChange.RelativeTangent.exists_point J hJ p g l hr hb
    refine ⟨v, ?_⟩
    apply TangentBaseChange.RelativeTangent.point_injective J hJ p' g'
    exact (TangentBaseChange.RelativeTangent.point_map J hJ p g p' g' f a hf hg v).trans ((congrArg (fun q => q ≫ f) hv).trans hl)

end RelativeTangent

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.TangentOpenRestriction
