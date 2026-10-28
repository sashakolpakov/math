import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MorphismSectionNaturality
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-! # Morphism Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MorphismSheaf

noncomputable section

/-! Actual morphisms between two fixed family pullbacks form a sheaf for every subcanonical topology on schemes, including fpqc, by their total-product section description. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem geometricFamilyMorphismFunctor_isSheaf_subcanonical
    {S : Scheme.{u}} (A B : Over S) (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical] :
    Presheaf.IsSheaf (J.over S) (Geometric.MorphismFunctor.geometricFamilyMorphismFunctor A B) := by
  have hc : (MorphismSectionEquivalence.familyTotalSpaceFunctor A).IsContinuous (J.over S) (J.over S) := by
    exact Functor.isContinuous_comp (Over.pullback A.hom) (Over.map A.hom)
      (J.over S) (J.over A.left) (J.over S)
  have hB : Presheaf.IsSheaf (J.over S) (yoneda.obj B) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  have h : Presheaf.IsSheaf (J.over S) ((MorphismSectionEquivalence.familyTotalSpaceFunctor A).op ⋙ yoneda.obj B) :=
    (MorphismSectionEquivalence.familyTotalSpaceFunctor A).op_comp_isSheaf_of_isSheaf (J.over S) (J.over S) _ hB
  exact (Presheaf.isSheaf_of_iso_iff (MorphismSectionNaturality.familyMorphismSectionIso A B)).mpr h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MorphismSheaf
