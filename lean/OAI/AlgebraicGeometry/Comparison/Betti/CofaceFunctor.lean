import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-! # Coface Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CofaceFunctor.Cech

noncomputable section

/-! Additive functors commute with the actual alternating-coface complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

variable {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  (G : A ⥤ B) [G.Additive]

def cofaceFunctorIso (X : CosimplicialObject A) :
    (G.mapHomologicalComplex (.up ℕ)).obj
      ((AlgebraicTopology.alternatingCofaceMapComplex A).obj X) ≅
    (AlgebraicTopology.alternatingCofaceMapComplex B).obj (X ⋙ G) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun i j h => by
    obtain rfl : i + 1 = j := h
    change 𝟙 _ ≫ (AlgebraicTopology.AlternatingCofaceMapComplex.obj (X ⋙ G)).d i (i + 1) =
      G.map ((AlgebraicTopology.AlternatingCofaceMapComplex.obj X).d i (i + 1)) ≫ 𝟙 _
    simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
      AlgebraicTopology.AlternatingCofaceMapComplex.objD, Category.id_comp, Category.comp_id,
      Functor.map_sum, Functor.map_zsmul]
    rfl)

def cofaceFunctorCompIso :
    AlgebraicTopology.alternatingCofaceMapComplex A ⋙ G.mapHomologicalComplex (.up ℕ) ≅
      (CosimplicialObject.whiskering A B).obj G ⋙ AlgebraicTopology.alternatingCofaceMapComplex B :=
  NatIso.ofComponents (cofaceFunctorIso G) (fun {X Y} f => by
    apply HomologicalComplex.Hom.ext
    funext n
    change G.map (f.app ⦋n⦌) ≫ 𝟙 _ = 𝟙 _ ≫ G.map (f.app ⦋n⦌)
    simp only [Category.comp_id, Category.id_comp])

end

end OAI.AlgebraicGeometry.Comparison.Betti.CofaceFunctor.Cech
