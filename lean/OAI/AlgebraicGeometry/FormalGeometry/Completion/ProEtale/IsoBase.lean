import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.EtaleRestriction

/-! # Iso Base -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.IsoBase.Construction

noncomputable section

/-!
# Completion: composition and isomorphic changes of base in the actual sites

The comparison maps are identity maps on the underlying schemes. An
isomorphism of bases induces an actual equivalence of pro-étale sites.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

local instance : MorphismProperty.IsStableUnderComposition (@WeaklyEtale.{u}) :=
  (inferInstance : MorphismProperty.IsMultiplicative (@WeaklyEtale.{u})).toIsStableUnderComposition

variable {X Y Z : Scheme.{u}}

/-- Composition of actual site functors agrees with composition of structure morphisms. -/
def proEtComposeCompIso (f : X ⟶ Y) (hf : WeaklyEtale f) (g : Y ⟶ Z) (hg : WeaklyEtale g) :
    EtaleRestriction.Construction.proEtCompose f hf ⋙ EtaleRestriction.Construction.proEtCompose g hg ≅
      EtaleRestriction.Construction.proEtCompose (f ≫ g) (MorphismProperty.comp_mem _ _ _ hf hg) :=
  (MorphismProperty.Over.mapComp (P := @WeaklyEtale) ⊤ hf hg).symm

/-- An isomorphism of scheme bases induces an equivalence of the actual sites. -/
def proEtIsoBaseEquivalence (e : X ≅ Y) : X.ProEt ≌ Y.ProEt where
  functor := EtaleRestriction.Construction.proEtCompose e.hom inferInstance
  inverse := EtaleRestriction.Construction.proEtCompose e.inv inferInstance
  unitIso :=
    (MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X (e.hom ≫ e.inv) e.hom_inv_id).symm ≪≫
      (proEtComposeCompIso e.hom inferInstance e.inv inferInstance).symm
  counitIso :=
    proEtComposeCompIso e.inv inferInstance e.hom inferInstance ≪≫
      MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ Y (e.inv ≫ e.hom) e.inv_hom_id
  functor_unitIso_comp U := by
    apply MorphismProperty.Over.Hom.ext
    change (𝟙 U.left ≫ 𝟙 U.left) ≫ (𝟙 U.left ≫ 𝟙 U.left) = 𝟙 U.left
    simp

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.IsoBase.Construction
