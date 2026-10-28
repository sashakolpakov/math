import OAI.AlgebraicGeometry.FormalGeometry.Completion.FlatPicardDescent

/-! # Picard Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.PicardDescent

noncomputable section

/-! Products of proper structure-preserving morphisms retain faithful
Picard pullback when the required projections are flat. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

variable {X Y X' Y' S : Scheme.{u}}

def productModificationMap (f : X ⟶ S) (g : Y ⟶ S) (p : X' ⟶ X) (q : Y' ⟶ Y) :
    pullback (p ≫ f) (q ≫ g) ⟶ pullback f g :=
  pullback.map _ _ _ _ p q (𝟙 S) (by simp) (by simp)

theorem productModificationMap_factor (f : X ⟶ S) (g : Y ⟶ S)
    (p : X' ⟶ X) (q : Y' ⟶ Y) :
    productModificationMap f g p q =
      PullbackCompositionMap.Construction.pullbackCompositionMap f p (q ≫ g) ≫ (pullbackSymmetry f (q ≫ g)).hom ≫
        PullbackCompositionMap.Construction.pullbackCompositionMap g q f ≫ (pullbackSymmetry g f).hom := by
  apply pullback.hom_ext <;> simp [productModificationMap, PullbackCompositionMap.Construction.pullbackCompositionMap, pullback.map]

theorem productModificationMap_app_isIso (f : X ⟶ S) (g : Y ⟶ S)
    (p : X' ⟶ X) (q : Y' ⟶ Y) [IsProper p] [IsProper q]
    [Flat f] [Flat (q ≫ g)]
    (hp : ∀ U : X.Opens, IsIso (p.app U)) (hq : ∀ U : Y.Opens, IsIso (q.app U))
    (V : (pullback f g).Opens) : IsIso ((productModificationMap f g p q).app V) := by
  let hleft (W : (pullback f (q ≫ g)).Opens) :
      IsIso ((PullbackCompositionMap.Construction.pullbackCompositionMap f p (q ≫ g)).app W) :=
    FlatPicardDescent.Construction.pullbackCompositionMap_app_isIso f p (q ≫ g) hp W
  let hright (W : (pullback g f).Opens) :
      IsIso ((PullbackCompositionMap.Construction.pullbackCompositionMap g q f).app W) :=
    FlatPicardDescent.Construction.pullbackCompositionMap_app_isIso g q f hq W
  have := hright ((pullbackSymmetry g f).hom ⁻¹ᵁ V)
  have := hleft ((pullbackSymmetry f (q ≫ g)).hom ⁻¹ᵁ
    (PullbackCompositionMap.Construction.pullbackCompositionMap g q f ⁻¹ᵁ ((pullbackSymmetry g f).hom ⁻¹ᵁ V)))
  rw [productModificationMap_factor]
  simp only [Scheme.Hom.comp_app, Scheme.Hom.comp_preimage]
  infer_instance

theorem productModificationMap_picard_injective (f : X ⟶ S) (g : Y ⟶ S)
    (p : X' ⟶ X) (q : Y' ⟶ Y) [IsProper p] [IsProper q]
    [Flat f] [Flat (q ≫ g)]
    (hp : ∀ U : X.Opens, IsIso (p.app U)) (hq : ∀ U : Y.Opens, IsIso (q.app U)) :
    Function.Injective (Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (productModificationMap f g p q)) :=
  FlatPicardDescent.Construction.picardPullback_injective_of_app_isIso _ (productModificationMap_app_isIso f g p q hp hq)

theorem pullback_map_app_isIso (f : X ⟶ S) (g : Y ⟶ S)
    (f' : X' ⟶ S) (g' : Y' ⟶ S) (p : X' ⟶ X) (q : Y' ⟶ Y)
    (hf : f' ≫ 𝟙 S = p ≫ f) (hg : g' ≫ 𝟙 S = q ≫ g)
    [IsProper p] [IsProper q] [Flat f] [Flat g']
    (hp : ∀ U : X.Opens, IsIso (p.app U)) (hq : ∀ U : Y.Opens, IsIso (q.app U))
    (V : (pullback f g).Opens) :
    IsIso ((pullback.map f' g' f g p q (𝟙 S) hf hg).app V) := by
  simp only [Category.comp_id] at hf hg
  subst f'
  subst g'
  exact productModificationMap_app_isIso f g p q hp hq V

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.PicardDescent
