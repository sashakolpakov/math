import OAI.NumberTheory.PadicHodge.GeometricComparison.BasisSheafificationTo
import Mathlib.CategoryTheory.Sites.Whiskering

/-! # Basis Sheafification Composition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BasisSheafificationComposition.BasisSheafification

noncomputable section

/-! A coefficient functor preserving sheaves carries agreement on a basis to the corresponding sheafification comparison. -/

open _root_.CategoryTheory _root_.TopologicalSpace

universe u v u' v' w z

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {X : TopCat.{w}} {ι : Type z}
  (B : ι → Opens X) (hB : Opens.IsBasis (Set.range B))
  (P : X.Presheaf C) (F : TopCat.Sheaf C X)
  (e : (inducedFunctor B).op ⋙ P ≅ (inducedFunctor B).op ⋙ F.obj)
  (G : C ⥤ D) [(Opens.grothendieckTopology X).HasSheafCompose G]

def compBasisIso : (inducedFunctor B).op ⋙ (P ⋙ G) ≅
    (inducedFunctor B).op ⋙ ((sheafCompose (Opens.grothendieckTopology X) G).obj F).obj :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e G ≪≫ Functor.associator _ _ _

variable [HasWeakSheafify (Opens.grothendieckTopology X) D]

def compIso : (presheafToSheaf (Opens.grothendieckTopology X) D).obj (P ⋙ G) ≅
    (sheafCompose (Opens.grothendieckTopology X) G).obj F :=
  BasisSheafificationTo.BasisSheafification.iso B hB (P ⋙ G) ((sheafCompose (Opens.grothendieckTopology X) G).obj F)
    (compBasisIso B P F e G)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BasisSheafificationComposition.BasisSheafification
