import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CommonRefinement

/-! # Common Refinement Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CommonRefinementNaturality

noncomputable section

/-! The relative extension through a common Čech refinement commutes
with maps of the original coefficient complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex

private theorem inverse_naturality {D : Type*} [Category D] {A B C E : D}
    (a : A ⟶ B) (b : C ⟶ E) (e : A ⟶ C) (f : B ⟶ E)
    [IsIso e] [IsIso f] (h : a ≫ f = e ≫ b) : b ≫ inv f = inv e ≫ a := by
  simpa only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id,
    Category.comp_id] using congrArg (fun z => inv e ≫ z ≫ inv f) h.symm

private theorem composition_naturality {D : Type*} [Category D]
    {A₀ A₁ B₀ B₁ C₀ C₁ T₀ T₁ : D}
    (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (c : C₀ ⟶ C₁) (d : T₀ ⟶ T₁)
    (r₀ : A₀ ⟶ B₀) (r₁ : A₁ ⟶ B₁) (s₀ : C₀ ⟶ B₀) (s₁ : C₁ ⟶ B₁)
    (e₀ : C₀ ⟶ T₀) (e₁ : C₁ ⟶ T₁) [IsIso s₀] [IsIso s₁]
    (hr : a ≫ r₁ = r₀ ≫ b) (hs : c ≫ s₁ = s₀ ≫ b) (he : c ≫ e₁ = e₀ ≫ d) :
    a ≫ (r₁ ≫ inv s₁ ≫ e₁) = (r₀ ≫ inv s₀ ≫ e₀) ≫ d := by
  calc
    _ = (a ≫ r₁) ≫ inv s₁ ≫ e₁ := by simp only [Category.assoc]
    _ = (r₀ ≫ b) ≫ inv s₁ ≫ e₁ := by rw [hr]
    _ = r₀ ≫ (b ≫ inv s₁) ≫ e₁ := by simp only [Category.assoc]
    _ = r₀ ≫ (inv s₀ ≫ c) ≫ e₁ := by rw [inverse_naturality c b s₀ s₁ hs]
    _ = _ := by simp only [Category.assoc]; rw [he]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
variable {X : TopCat.{u}} (U : Opens X)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (V : ι → Opens X) (W : κ → Opens X) (T : ν → Opens X)
  (r : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι V)
  (s : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk κ W)
  {D : Type (u+1)} [Category.{u} D] [Abelian D] [HasLimitsOfSize.{u,u} D]
  [HasCoproducts.{0} D]
  {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ} (a : K ⟶ L) (n : ℕ)
  [IsIso (Refinement.homology U W T s K n)]
  [IsIso (Refinement.homology U W T s L n)]

theorem naturality : homologyMap (Total.sourceMap U V a) n ≫
    CommonRefinement.comparison U V W T r s L n =
      CommonRefinement.comparison U V W T r s K n ≫ homologyMap (Total.targetMap U W a) n :=
  composition_naturality _ _ _ _ _ _ _ _ _ _
    (Refinement.homology_naturality U V T r a n)
    (Refinement.homology_naturality U W T s a n)
    (Total.homology_naturality U W a n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CommonRefinementNaturality
