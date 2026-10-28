import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.IsomorphismFunctor

/-! # Level Iso Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.LevelIsoFunctor

noncomputable section

/-! Complete polarized full-level isomorphisms form a functor on all test schemes. A proved universal graph bound identifies it with the bounded isomorphism functor. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
universe u

local instance unboundedIsoPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Flat A.hom] :
    Flat ((Over.pullback f).obj A).hom := inferInstanceAs (Flat (Limits.pullback.snd A.hom f))
local instance unboundedIsoPullbackFP {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S)
    [LocallyOfFinitePresentation A.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj A).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd A.hom f))
local instance unboundedIsoPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom f))

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

def familyLevelIsoFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.unop.hom) (B.pullback T.unop.hom)
  map c := TypeCat.ofHom (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint A B c.unop)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro e
    apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
    exact (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom A B (𝟙 T.unop) e).trans
      (Geometric.MorphismFunctor.geometricFamilyMorphismBaseChange_id T.unop e.abelian.hom)
  map_comp c d := by
    apply ConcreteCategory.hom_ext
    intro e
    apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
    exact (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom A B (d.unop ≫ c.unop) e).trans
      ((Geometric.MorphismFunctor.geometricFamilyMorphismBaseChange_composition d.unop c.unop e.abelian.hom).symm.trans
        ((congrArg (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange d.unop)
          (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom A B c.unop e).symm).trans
          (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom A B d.unop
            (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint A B c.unop e)).symm))

def boundedFamilyLevelIsoForgetEquiv {n : ℕ}
    (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) (h : ∀ (T : Over S) (e : Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom)),
      Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P e.abelian.hom)
    (T : Over S) : BoundedModuli.IsomorphismFunctor.BoundedFamilyLevelIso A B j P T ≃ Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom) where
  toFun := Subtype.val
  invFun e := ⟨e, h T e⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

def boundedFamilyLevelIsoForgetIso {n : ℕ}
    (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) (h : ∀ (T : Over S) (e : Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom)),
      Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P e.abelian.hom) :
    BoundedModuli.IsomorphismFunctor.boundedFamilyLevelIsoFunctor A B j P ≅ familyLevelIsoFunctor A B :=
  NatIso.ofComponents (fun T => (boundedFamilyLevelIsoForgetEquiv A B j P h T.unop).toIso)
    (fun _ => rfl)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.LevelIsoFunctor
