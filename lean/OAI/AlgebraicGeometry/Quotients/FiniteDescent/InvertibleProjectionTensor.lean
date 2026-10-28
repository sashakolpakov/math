import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Invertible Projection Tensor -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvertibleProjectionTensor.Construction.InvertibleProjection

noncomputable section

/-! The projection formula for tensor-invertible objects follows from
uniqueness of right adjoints. This will descend line-bundle trivializations. -/

open _root_.CategoryTheory MonoidalCategory

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

def tensorEquivalence (P Q : C) (ePQ : P ⊗ Q ≅ 𝟙_ C) (eQP : Q ⊗ P ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorLeft P) (tensorLeft Q)
    ((leftUnitorNatIso C).symm ≪≫ (tensoringLeft C).mapIso eQP.symm ≪≫ tensorLeftTensor Q P)
    ((tensorLeftTensor P Q).symm ≪≫ (tensoringLeft C).mapIso ePQ ≪≫ leftUnitorNatIso C)

def mapPairing (F : C ⥤ D) [F.Monoidal] {P Q : C} (e : P ⊗ Q ≅ 𝟙_ C) :
    F.obj P ⊗ F.obj Q ≅ 𝟙_ D :=
  Functor.Monoidal.μIso F P Q ≪≫ F.mapIso e ≪≫ (Functor.Monoidal.εIso F).symm

def iso (F : C ⥤ D) [F.Monoidal] (G : D ⥤ C) (a : F ⊣ G)
    (L L' : C) (e : L ⊗ L' ≅ 𝟙_ C) (e' : L' ⊗ L ≅ 𝟙_ C) (N : D) :
    L ⊗ G.obj N ≅ G.obj (F.obj L ⊗ N) := by
  let b : tensorLeft L' ⊣ tensorLeft L := (tensorEquivalence L' L e' e).toAdjunction
  let c : tensorLeft (F.obj L') ⊣ tensorLeft (F.obj L) :=
    (tensorEquivalence (F.obj L') (F.obj L) (mapPairing F e') (mapPairing F e)).toAdjunction
  exact (Adjunction.rightAdjointUniq (b.comp a)
    ((a.comp c).ofNatIsoLeft (Functor.Monoidal.commTensorLeft F L'))).app N

def descend_trivial (F : C ⥤ D) [F.Monoidal] (G : D ⥤ C) (a : F ⊣ G)
    (L L' : C) (e : L ⊗ L' ≅ 𝟙_ C) (e' : L' ⊗ L ≅ 𝟙_ C)
    (hG : G.obj (𝟙_ D) ≅ 𝟙_ C) (hL : F.obj L ≅ 𝟙_ D) : L ≅ 𝟙_ C :=
  (ρ_ L).symm ≪≫ (tensorLeft L).mapIso hG.symm ≪≫ iso F G a L L' e e' (𝟙_ D) ≪≫
    G.mapIso ((ρ_ (F.obj L)) ≪≫ hL) ≪≫ hG

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvertibleProjectionTensor.Construction.InvertibleProjection
