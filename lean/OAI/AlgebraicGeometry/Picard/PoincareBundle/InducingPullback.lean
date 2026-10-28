import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingClass

/-! # Inducing Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingPullback.Bundle

noncomputable section

/-! The quotient inducing line gives an actual product-line recovery isomorphism, before any Picard representation is chosen. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingClass.Bundle

/-- Two factorizations of the same scheme map induce the same Picard pullback. -/
theorem pullback_square {W X Y Z : Scheme.{u}} (p : W ⟶ X) (r : X ⟶ Z)
    (q : W ⟶ Y) (s : Y ⟶ Z) (h : p ≫ r = q ≫ s) (c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Z) :
    Homomorphisms.SchemePullback.Construction.schemePicardPullback p (Homomorphisms.SchemePullback.Construction.schemePicardPullback r c) =
      Homomorphisms.SchemePullback.Construction.schemePicardPullback q (Homomorphisms.SchemePullback.Construction.schemePicardPullback s c) :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp p r c).symm.trans
    ((congrArg (fun t => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass t c) h).trans (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp q s c))

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)

/-- Difference classes commute with pullback by the actual group-homomorphism product. -/
theorem lineClass_pullback :
    Homomorphisms.SchemePullback.Construction.schemePicardPullback (f ⊗ₘ f).left (InducingClass.Bundle.lineClass B L) = InducingClass.Bundle.lineClass A (L.pullback f.left) := by
  rw [InducingClass.Bundle.lineClass, map_div, map_div, InducingClass.Bundle.lineClass]
  have hm : (f ⊗ₘ f).left ≫ μ[B].left = μ[A].left ≫ f.left :=
    (congrArg Over.Hom.left (IsMonHom.mul_hom f)).symm
  have h1 : (f ⊗ₘ f).left ≫ (fst B B).left = (fst A A).left ≫ f.left :=
    Over.tensorHom_left_fst _ _ _ _
  have h2 : (f ⊗ₘ f).left ≫ (snd B B).left = (snd A A).left ≫ f.left :=
    Over.tensorHom_left_snd _ _ _ _
  exact congrArg₂ (fun x y => x / y)
    (congrArg₂ (fun x y => x / y)
      (pullback_square _ _ _ _ hm (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
      (pullback_square _ _ _ _ h1 (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)))
    (pullback_square _ _ _ _ h2 (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))

/-- The comparison is an actual isomorphism of line sheaves. -/
def pullbackIso :
    (Scheme.Modules.pullback (f ⊗ₘ f).left).obj (InducingClass.Bundle.line B L).sheaf ≅ (InducingClass.Bundle.line A (L.pullback f.left)).sheaf :=
  Classical.choice (Quotient.exact
    ((congrArg (Homomorphisms.SchemePullback.Construction.schemePicardPullback (f ⊗ₘ f).left) (InducingClass.Bundle.classOf_line B L)).trans
      ((lineClass_pullback f L).trans (InducingClass.Bundle.classOf_line A (L.pullback f.left)).symm)))

/-- An inducing formula on the source recovers that source line from the quotient's actual difference line. -/
def recoveryIso (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left)
    (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf ((L.pullback f.left).pullback (fst A A).left).sheaf)
      ((L.pullback f.left).pullback (snd A A).left).sheaf ≅
        ((L.pullback f.left).pullback μ[A].left).sheaf) :
    (Scheme.Modules.pullback (f ⊗ₘ f).left).obj (InducingClass.Bundle.line B L).sheaf ≅ Q.sheaf :=
  Classical.choice (Quotient.exact
    ((congrArg (Homomorphisms.SchemePullback.Construction.schemePicardPullback (f ⊗ₘ f).left) (InducingClass.Bundle.classOf_line B L)).trans
      ((lineClass_pullback f L).trans (InducingClass.Bundle.class_eq_of_formula A (L.pullback f.left) Q e).symm)))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingPullback.Bundle
