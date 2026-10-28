import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-! # Module Pullback Hom -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModulePullbackHom

noncomputable section

/-! Relating the concrete module pullback maps to the native pseudofunctor
coherence, so repeated restrictions retain all composition equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback

def modulePullbackFunctor : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Scheme.Modules.pseudofunctor.comp Bicategory.Adj.forget₁

variable {X Y Z : Scheme.{u}} {M N : Z.Modules}

theorem pullbackHomTo_eq_pullHom (f : X ⟶ Y) (g : Y ⟶ Z) (p : X ⟶ Z) (h : f ≫ g = p)
    (q : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N) :
    FramedPullback.pullbackHomTo f g p h q = pullHom (F := modulePullbackFunctor) q f p p h h := by
  subst p
  rfl

theorem pullbackHomTo_identity (g : Y ⟶ Z)
    (q : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N) :
    FramedPullback.pullbackHomTo (𝟙 Y) g g (Category.id_comp g) q = q := by
  rw [pullbackHomTo_eq_pullHom]
  exact pullHom_id (F := modulePullbackFunctor) q

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModulePullbackHom
