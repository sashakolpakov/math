import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsOpenEquality
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTotal

/-! # Ordered Cech Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechReindex

noncomputable section

/-! A finite-product-preserving change of principal indices
preserves the actual supported-section edge in the ordered Čech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem inverse_square {A : Type*} [Category A]
    {S₁ S₂ T₁ T₂ C₁ C₂ : A}
    (s : S₁ ⟶ S₂) (i₁ : S₁ ⟶ T₁) (i₂ : S₂ ⟶ T₂) (d : T₁ ⟶ T₂)
    (e₁ : C₁ ≅ T₁) (e₂ : C₂ ≅ T₂) (c : C₁ ⟶ C₂)
    (h₁ : s ≫ i₂ = i₁ ≫ d) (h₂ : c ≫ e₂.hom = e₁.hom ≫ d) :
    s ≫ (i₂ ≫ e₂.inv) = (i₁ ≫ e₁.inv) ≫ c := by
  apply (cancel_mono e₂.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h₂, ← Category.assoc e₁.inv e₁.hom d, e₁.inv_hom_id, Category.id_comp]
  exact h₁

private theorem lift_square {A : Type*} [Category A]
    {S₁ S₂ C₁ C₂ T₁ T₂ : A}
    (s : S₁ ⟶ S₂) (a : S₁ ⟶ C₁) (b : S₂ ⟶ C₂) (t : C₁ ⟶ C₂)
    (i₁ : C₁ ⟶ T₁) (i₂ : C₂ ⟶ T₂) (m : T₁ ⟶ T₂)
    (h₁ : s ≫ b = a ≫ t) (h₂ : i₁ ≫ m = t ≫ i₂) :
    s ≫ (b ≫ i₂) = (a ≫ i₁) ≫ m := by
  rw [← Category.assoc, h₁, Category.assoc, ← h₂, ← Category.assoc]

universe u
variable (R : Type (u + 1)) [CommRing R] (X : TopCat.{u})
  {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteProducts r] (F : D ⥤ Opens X)
  {ι : Type u} [LinearOrder ι] (U : ι → C) (O : Opens X)

local instance coefficient_limits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 2, u + 1}
local instance coefficient_colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasColimitsOfSize.{u + 2, u + 1, 0, 0} R

theorem terminal_eq : (r ⋙ F).obj (⊤_ C) = F.obj (⊤_ D) :=
  le_antisymm (leOfHom (F.map (PreservesTerminal.iso r).hom))
    (leOfHom (F.map (PreservesTerminal.iso r).inv))

theorem terminal_inv : F.map (PreservesTerminal.iso r).inv =
    eqToHom (terminal_eq X r F).symm := Subsingleton.elim _ _

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 2} R)) ℕ)

def sourceIso :
    OrderedCechEdge.source.{u+1,u,u,u+2} R X (r ⋙ F) O K ≅
      OrderedCechEdge.source.{u+1,u,u,u+2} R X F O K :=
  SectionsOpenEquality.complexIso O ((r ⋙ F).obj (⊤_ C)) (F.obj (⊤_ D))
    (terminal_eq X r F) K

def totalIso :
    (OrderedCechEdge.bicomplex.{u+1,u,u,u+2} R X (r ⋙ F) U K).total (.up ℕ) ≅
      (OrderedCechEdge.bicomplex.{u+1,u,u,u+2} R X F (r.obj ∘ U) K).total (.up ℕ) :=
  AugmentedOrdered.CechReindexTotal.totalIso r U
    (OrderedCechEdge.presheafComplex.{u+1,u,u,u+2} R X F K)

theorem component (q : ℕ) :
    (sourceIso R X r F O K).hom.f q ≫
      OrderedCechEdge.component.{u+1,u,u,u+2} R X F (r.obj ∘ U) O K q =
    OrderedCechEdge.component.{u+1,u,u,u+2} R X (r ⋙ F) U O K q ≫
      (((AugmentedOrdered.CechReindexTotal.bicomplexIso r U
        (OrderedCechEdge.presheafComplex.{u+1,u,u,u+2} R X F K)).hom.f q).f 0) := by
  have h₁ := SectionsOpenEquality.inclusion
    O ((r ⋙ F).obj (⊤_ C)) (F.obj (⊤_ D)) (terminal_eq X r F) (K.X q)
  have h₂ := AugmentedOrdered.CechReindex.zero r U (F.op ⋙ (K.X q).obj)
  change _ = _ ≫ (K.X q).obj.map (F.map (PreservesTerminal.iso r).inv).op at h₂
  rw [terminal_inv X r F] at h₂
  exact inverse_square _ _ _ _ _ _ _ h₁ h₂

variable (hO : ∀ i, F.obj (r.obj (U i)) ≤ O)

theorem edge :
    (sourceIso R X r F O K).hom ≫ OrderedCechEdge.map.{u+1,u,u,u+2} R X F (r.obj ∘ U) O K hO =
      OrderedCechEdge.map.{u+1,u,u,u+2} R X (r ⋙ F) U O K hO ≫ (totalIso R X r F U K).hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  change (sourceIso R X r F O K).hom.f q ≫
      (OrderedCechEdge.component.{u+1,u,u,u+2} R X F (r.obj ∘ U) O K q ≫
        (OrderedCechEdge.bicomplex.{u+1,u,u,u+2} R X F (r.obj ∘ U) K).ιTotal (.up ℕ) q 0 q (by simp)) =
    (OrderedCechEdge.component.{u+1,u,u,u+2} R X (r ⋙ F) U O K q ≫
        (OrderedCechEdge.bicomplex.{u+1,u,u,u+2} R X (r ⋙ F) U K).ιTotal (.up ℕ) q 0 q (by simp)) ≫
      (HomologicalComplex₂.total.map
        (AugmentedOrdered.CechReindexTotal.bicomplexIso r U
          (OrderedCechEdge.presheafComplex.{u+1,u,u,u+2} R X F K)).hom (.up ℕ)).f q
  exact lift_square _ _ _ _ _ _ _ (component R X r F U O K q)
    (HomologicalComplex₂.ιTotal_map _ _ _ _ q 0 q (by simp))

theorem extension (hC : (r ⋙ F).obj (⊤_ C) ⊔ O = ⊤) (hD : F.obj (⊤_ D) ⊔ O = ⊤) :
    (sourceIso R X r F O K).hom ≫
      SectionsExcision.extensionComplex O (F.obj (⊤_ D)) hD K =
    SectionsExcision.extensionComplex O ((r ⋙ F).obj (⊤_ C)) hC K :=
  SectionsOpenEquality.complex_extension O ((r ⋙ F).obj (⊤_ C)) (F.obj (⊤_ D))
    (terminal_eq X r F) K hC hD

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechReindex
