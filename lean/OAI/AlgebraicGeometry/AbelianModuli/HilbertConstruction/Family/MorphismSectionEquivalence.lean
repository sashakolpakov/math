import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismFunctor

/-! # Morphism Section Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MorphismSectionEquivalence

noncomputable section

/-! A morphism between two family pullbacks is equivalent to a morphism from their actual total parameter product to the original target. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}}

def familyTotalSpaceFunctor (A : Over S) : Over S ⥤ Over S :=
  Over.pullback A.hom ⋙ Over.map A.hom

def familyTotalSpaceSwapIso (A T : Over S) :
    (familyTotalSpaceFunctor A).obj T ≅ (Over.map T.hom).obj ((Over.pullback T.hom).obj A) := by
  refine Over.isoMk (pullbackSymmetry T.hom A.hom) ?_
  change (pullbackSymmetry T.hom A.hom).hom ≫ (pullback.snd A.hom T.hom ≫ T.hom) =
    pullback.snd T.hom A.hom ≫ A.hom
  rw [← Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.condition]

def familyMorphismSectionEquiv (A B T : Over S) :
    ((Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B) ≃
      ((familyTotalSpaceFunctor A).obj T ⟶ B) :=
  ((Over.mapPullbackAdj T.hom).homEquiv ((Over.pullback T.hom).obj A) B).symm.trans
    (Iso.homCongr (familyTotalSpaceSwapIso A T).symm (Iso.refl B))

theorem familyMorphismSectionEquiv_left (A B T : Over S)
    (p : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B) :
    (familyMorphismSectionEquiv A B T p).left =
      (pullbackSymmetry T.hom A.hom).hom ≫ p.left ≫ pullback.fst B.hom T.hom := by
  change ((pullbackSymmetry T.hom A.hom).hom ≫ (p.left ≫ pullback.fst B.hom T.hom)) ≫ 𝟙 _ = _
  exact Category.comp_id _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MorphismSectionEquivalence
