import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PointedMapParameters

/-! # Pointed Map Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PointedMapRepresentation

noncomputable section

/-! The bounded pointed-map parameter naturally represents the actual identity-preserving morphism functor on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {A B : Over S} {n : ℕ}
variable [IsProper A.hom] [Smooth A.hom] [IsSeparated B.hom] [MonObj A] [MonObj B]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)

def boundedPointedMapSubfunctor : Subfunctor (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor j P) where
  obj T := {f | η[(Over.pullback T.unop.hom).obj A] ≫ f.val = η[(Over.pullback T.unop.hom).obj B]}
  map c f hf := by
    apply (PointedMapBaseChange.geometricFamilyMorphismBaseChange_pointed_iff c.unop f.val).mpr
    exact (MappedMonoidHomEquations.mappedMonoidHom_one_iff (Over.pullback c.unop.left) f.val).mpr
      (congrArg (Over.pullback c.unop.left).map hf)

def boundedPointedMapFunctor : (Over S)ᵒᵖ ⥤ Type u := (boundedPointedMapSubfunctor j P).toFunctor

def boundedPointedMapClassifyingIso :
    yoneda.obj (PointedMapParameters.boundedPointedMapParameter j P) ≅ boundedPointedMapFunctor j P :=
  NatIso.ofComponents (fun T => (PointedMapParameters.boundedPointedMapParameterPointEquiv j P T.unop).toIso) (by
    intro T U c
    apply ConcreteCategory.hom_ext
    intro y
    apply Subtype.ext
    change (PointedMapParameters.boundedPointedMapParameterPointEquiv j P U.unop (c.unop ≫ y)).val =
      (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor j P).map c (PointedMapParameters.boundedPointedMapParameterPointEquiv j P T.unop y).val
    rw [PointedMapParameters.boundedPointedMapParameterPointEquiv_val, PointedMapParameters.boundedPointedMapParameterPointEquiv_val]
    exact (congrArg (HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv j P U.unop)
      (Category.assoc c.unop y (PointedMapParameters.boundedPointedMapParameterInclusion j P))).trans
      (OperationParameterNaturality.smoothEmbeddedGraphParameterMorphismEquiv_natural j P c.unop
        (y ≫ PointedMapParameters.boundedPointedMapParameterInclusion j P)))

theorem boundedPointedMapPoint_natural {U T : Over S} (c : U ⟶ T) (p : T ⟶ PointedMapParameters.boundedPointedMapParameter j P) :
    PointedMapParameters.boundedPointedMapParameterPointEquiv j P U (c ≫ p) =
      (boundedPointedMapFunctor j P).map c.op (PointedMapParameters.boundedPointedMapParameterPointEquiv j P T p) :=
  ConcreteCategory.congr_hom (CC := fun X : Type u => X)
    ((boundedPointedMapClassifyingIso j P).hom.naturality c.op) p

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PointedMapRepresentation
