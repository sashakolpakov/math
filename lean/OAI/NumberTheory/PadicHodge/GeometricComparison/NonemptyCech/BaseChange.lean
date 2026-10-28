import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange

/-! # Base Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.BaseChange.NonemptyCechBaseChange

noncomputable section

/-! The original Čech base-change construction only needs nonempty finite
products in its indexing categories. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial _root_.AlgebraicTopology

universe w v vD vA u uD uA
variable {A : Type uA} [Category.{vA} A] [HasProducts.{w} A]

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasBinaryProducts D]
  (F : C ⥤ D) [PreservesFiniteLimits F] {ι : Type w} (U : ι → C) (P : Dᵒᵖ ⥤ A)

def componentIso (n : SimplexCategory) :
    (∏ᶜ fun t : Fin (n.len + 1) → ι => P.obj (op (F.obj (∏ᶜ (U ∘ t))))) ≅
      ∏ᶜ fun t : Fin (n.len + 1) → ι => P.obj (op (∏ᶜ (fun i => F.obj (U (t i))))) :=
  Pi.mapIso (fun t => P.mapIso (PreservesProduct.iso F (U ∘ t)).symm.op)

def cosimplicialIso :
    (FormalCoproduct.cosimplicialObjectFunctor (IntegralComparison.NonemptyCechNerve.nerve U)).obj (F.op ⋙ P) ≅
      (FormalCoproduct.cosimplicialObjectFunctor (IntegralComparison.NonemptyCechNerve.nerve (F.obj ∘ U))).obj P :=
  NatIso.ofComponents (componentIso F U P) (by
    intro n m f
    let En := (IntegralComparison.NonemptyCechNerve.nerve U).obj (op n)
    let Em := (IntegralComparison.NonemptyCechNerve.nerve U).obj (op m)
    let φ := (IntegralComparison.NonemptyCechNerve.nerve U).map f.op
    let ψ := (IntegralComparison.NonemptyCechNerve.nerve (F.obj ∘ U)).map f.op
    apply AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.productIso_natural
      (fun t => P.mapIso (PreservesProduct.iso F (U ∘ t)).symm.op)
      (fun t => P.mapIso (PreservesProduct.iso F (U ∘ t)).symm.op) φ.f
      (fun t => P.map (F.map (φ.φ t)).op) (fun t => P.map (ψ.φ t).op)
    intro t
    change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
    exact (P.map_comp _ _).symm.trans
      ((congrArg P.map (Subsingleton.elim _ _)).trans (P.map_comp _ _)))

variable [Preadditive A]

/-- Inverse image of the family and precomposition of coefficients give isomorphic Čech complexes. -/
def complexIso :
    (IntegralComparison.NonemptyCechNerve.complexFunctor U).obj (F.op ⋙ P) ≅ (IntegralComparison.NonemptyCechNerve.complexFunctor (F.obj ∘ U)).obj P :=
  (alternatingCofaceMapComplex A).mapIso (cosimplicialIso F U P)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.BaseChange.NonemptyCechBaseChange
