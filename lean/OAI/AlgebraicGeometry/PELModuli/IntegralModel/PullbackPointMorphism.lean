import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

/-! # Pullback Point Morphism -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PullbackPointMorphism

noncomputable section

/-! Morphisms between composite pullbacks induce morphisms between the
corresponding iterated pullbacks, with identity, composition, and
restriction proved from the pseudofunctor coherence. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'
variable {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {X X' Z : C} (v : X' ⟶ X) (L : F.obj (.mk (op X)))

def pullbackPointMorphism (x y : Z ⟶ X')
    (h : (F.map (x ≫ v).op.toLoc).toFunctor.obj L ⟶ (F.map (y ≫ v).op.toLoc).toFunctor.obj L) :
    (F.map x.op.toLoc).toFunctor.obj ((F.map v.op.toLoc).toFunctor.obj L) ⟶
      (F.map y.op.toLoc).toFunctor.obj ((F.map v.op.toLoc).toFunctor.obj L) :=
  (F.mapComp' v.op.toLoc x.op.toLoc (x ≫ v).op.toLoc rfl).inv.toNatTrans.app L ≫ h ≫
    (F.mapComp' v.op.toLoc y.op.toLoc (y ≫ v).op.toLoc rfl).hom.toNatTrans.app L

theorem pullbackPointMorphism_identity (x : Z ⟶ X') :
    pullbackPointMorphism F v L x x (𝟙 _) = 𝟙 _ := by
  simp [pullbackPointMorphism]

theorem pullbackPointMorphism_comp (x y z : Z ⟶ X')
    (h : (F.map (x ≫ v).op.toLoc).toFunctor.obj L ⟶ (F.map (y ≫ v).op.toLoc).toFunctor.obj L)
    (k : (F.map (y ≫ v).op.toLoc).toFunctor.obj L ⟶ (F.map (z ≫ v).op.toLoc).toFunctor.obj L) :
    pullbackPointMorphism F v L x y h ≫ pullbackPointMorphism F v L y z k =
      pullbackPointMorphism F v L x z (h ≫ k) := by
  simp [pullbackPointMorphism, ← reassoc_of% Cat.Hom₂.comp_app]

theorem pullbackPointMorphism_restrict {Z' : C} (x y : Z ⟶ X') (g : Z' ⟶ Z) (x' y' : Z' ⟶ X')
    (hx : g ≫ x = x') (hy : g ≫ y = y')
    (h : (F.map (x ≫ v).op.toLoc).toFunctor.obj L ⟶ (F.map (y ≫ v).op.toLoc).toFunctor.obj L) :
    pullHom (pullbackPointMorphism F v L x y h) g x' y' hx hy =
      pullbackPointMorphism F v L x' y'
        (pullHom h g (x' ≫ v) (y' ≫ v)
          (by rw [← Category.assoc, hx]) (by rw [← Category.assoc, hy])) := by
  dsimp [pullbackPointMorphism, pullHom]
  simp only [Functor.map_comp, Category.assoc]
  erw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc
    v.op.toLoc x.op.toLoc g.op.toLoc (x ≫ v).op.toLoc x'.op.toLoc (x' ≫ v).op.toLoc
    rfl (by rw [← hx]; rfl) rfl,
    F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app
      v.op.toLoc y.op.toLoc g.op.toLoc (y ≫ v).op.toLoc y'.op.toLoc (y' ≫ v).op.toLoc
      rfl (by rw [← hy]; rfl) (by rw [← hy, Category.assoc]; rfl)]
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PullbackPointMorphism
