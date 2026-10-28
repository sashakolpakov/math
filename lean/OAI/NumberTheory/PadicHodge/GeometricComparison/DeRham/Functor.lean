import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Composition
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IsoCohomology

/-! # Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Functor

noncomputable section

/-! The actual de Rham pullbacks form a contravariant functor, including the identity law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {R : Type} [CommRing R]

theorem pullback_id (X : Over (Spec (CommRingCat.of R))) (n : ℕ) :
    Int.pullback (𝟙 X) n = LinearMap.id := by
  have hinj : Function.Injective (Int.pullback (𝟙 X) n) := by
    rw [← IsoCohomology.isoPullback_toLinearMap]
    exact (IsoCohomology.isoPullback (𝟙 X) n).injective
  have hh := Composition.pullback_comp (𝟙 X) (𝟙 X) n
  rw [Category.id_comp] at hh
  apply LinearMap.ext
  intro x
  apply hinj
  exact LinearMap.congr_fun hh x

def cohomologyFunctor (R : Type) [CommRing R] (n : ℕ) :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ ModuleCat.{1} R where
  obj X := AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X.unop n
  map f := ModuleCat.ofHom (Int.pullback f.unop n)
  map_id X := ModuleCat.hom_ext (pullback_id X.unop n)
  map_comp f g := ModuleCat.hom_ext (Composition.pullback_comp g.unop f.unop n).symm

theorem pullback_square {X Y X' Y' : Over (Spec (CommRingCat.of R))}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) (n : ℕ) :
    (Int.pullback f n).comp (Int.pullback b n) = (Int.pullback a n).comp (Int.pullback g n) :=
  (Composition.pullback_comp f b n).trans
    ((congrArg (fun k => Int.pullback k n) h).trans (Composition.pullback_comp a g n).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Functor
