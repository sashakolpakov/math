import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.ParameterPointMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.IsomorphismUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.EmbeddedMorphismFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismFunctor

/-! # Isomorphism Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.IsomorphismFunctor

noncomputable section

/-! Complete polarized full-level isomorphisms with a fixed embedded graph polynomial form an actual functor on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance boundedModuliPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) [Flat X.hom] :
    Flat ((Over.pullback f).obj X).hom := inferInstanceAs (Flat (Limits.pullback.snd X.hom f))

local instance boundedModuliPullbackFinitePresentation {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S)
    [LocallyOfFinitePresentation X.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj X).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd X.hom f))

local instance boundedModuliPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) [IsSeparated X.hom] :
    IsSeparated ((Over.pullback f).obj X).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd X.hom f))

variable {S : Scheme.{u}} {g N n : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ)

def BoundedFamilyLevelIso (T : Over S) :=
  {e : Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom) //
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P e.abelian.hom}

def BoundedFamilyLevelIso.pullback {T U : Over S} (c : U ⟶ T) (e : BoundedFamilyLevelIso A B j P T) :
    BoundedFamilyLevelIso A B j P U := by
  refine ⟨Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint A B c e.val, ?_⟩
  exact (congrArg (Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding U.hom j) P)
    (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom A B c e.val)).mpr
    (Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.geometricBaseChange c j e.val.abelian.hom P e.property)

def boundedFamilyLevelIsoFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := BoundedFamilyLevelIso A B j P T.unop
  map c := TypeCat.ofHom (BoundedFamilyLevelIso.pullback A B j P c.unop)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro e
    apply Subtype.ext
    apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
    exact (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom A B (𝟙 T.unop) e.val).trans
      (Geometric.MorphismFunctor.geometricFamilyMorphismBaseChange_id T.unop e.val.abelian.hom)
  map_comp c d := by
    apply ConcreteCategory.hom_ext
    intro e
    apply Subtype.ext
    apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
    exact (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom A B (d.unop ≫ c.unop) e.val).trans
      ((Geometric.MorphismFunctor.geometricFamilyMorphismBaseChange_composition d.unop c.unop e.val.abelian.hom).symm.trans
        ((congrArg (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange d.unop)
          (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom A B c.unop e.val).symm).trans
          (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom A B d.unop
            (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint A B c.unop e.val)).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.IsomorphismFunctor
