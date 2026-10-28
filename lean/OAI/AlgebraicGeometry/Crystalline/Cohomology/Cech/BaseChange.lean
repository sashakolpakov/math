import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange

noncomputable section

/-!
# Čech cochains under base change of a lattice of opens

A finite-limit-preserving functor between thin categories carries the
intersection diagram to the intersection diagram of the image family.
The product comparison isomorphisms identify the corresponding Čech
complexes. This is used for inverse image of opens under an open immersion.
-/

open _root_.CategoryTheory Limits Opposite Simplicial _root_.AlgebraicTopology

universe w v vD vA u uD uA

variable {A : Type uA} [Category.{vA} A] [HasProducts.{w} A]

theorem productIso_natural {α β : Type w} {X X' : α → A} {Y Y' : β → A}
    (eX : ∀ i, X i ≅ X' i) (eY : ∀ j, Y j ≅ Y' j) (f : β → α)
    (a : ∀ j, X (f j) ⟶ Y j) (b : ∀ j, X' (f j) ⟶ Y' j)
    (h : ∀ j, a j ≫ (eY j).hom = (eX (f j)).hom ≫ b j) :
    (Pi.lift (fun j => Pi.π X (f j) ≫ a j)) ≫ (Pi.mapIso eY).hom =
      (Pi.mapIso eX).hom ≫ Pi.lift (fun j => Pi.π X' (f j) ≫ b j) := by
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, Pi.mapIso_hom_π, Pi.lift_comp_π, Pi.lift_comp_π_assoc,
    Pi.mapIso_hom_π_assoc, h]

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasFiniteProducts D]
  (F : C ⥤ D) [PreservesFiniteLimits F] {ι : Type w} (U : ι → C) (P : Dᵒᵖ ⥤ A)

def componentIso (n : SimplexCategory) :
    (∏ᶜ fun t : Fin (n.len + 1) → ι => P.obj (op (F.obj (∏ᶜ (U ∘ t))))) ≅
      ∏ᶜ fun t : Fin (n.len + 1) → ι => P.obj (op (∏ᶜ (fun i => F.obj (U (t i))))) :=
  Pi.mapIso (fun t => P.mapIso (PreservesProduct.iso F (U ∘ t)).symm.op)

def cosimplicialIso :
    (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj (F.op ⋙ P) ≅
      (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι (F.obj ∘ U)).cech).obj P :=
  NatIso.ofComponents (componentIso F U P) (by
    intro n m f
    let En := (FormalCoproduct.mk ι U).cech.obj (op n)
    let Em := (FormalCoproduct.mk ι U).cech.obj (op m)
    let φ := (FormalCoproduct.mk ι U).cech.map f.op
    let ψ := (FormalCoproduct.mk ι (F.obj ∘ U)).cech.map f.op
    apply productIso_natural
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
    (cechComplexFunctor U).obj (F.op ⋙ P) ≅ (cechComplexFunctor (F.obj ∘ U)).obj P :=
  (alternatingCofaceMapComplex A).mapIso (cosimplicialIso F U P)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange
