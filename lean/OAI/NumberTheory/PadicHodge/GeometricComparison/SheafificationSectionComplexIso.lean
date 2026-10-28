import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Additive

/-! # Sheafification Section Complex Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationSectionComplexIso.SheafificationSectionComplex

noncomputable section

/-! When the canonical sheafification maps are invertible on an open, evaluating a presheaf complex and its sheafification gives canonically isomorphic complexes. -/

open _root_.CategoryTheory

universe u v u' v' w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasSheafify J D]
  {ι : Type w} (c : ComplexShape ι) (K : HomologicalComplex (Cᵒᵖ ⥤ D) c) (U : Cᵒᵖ)
  (hU : ∀ n, IsIso ((toSheafify J (K.X n)).app U))

def componentIso (n : ι) : (K.X n).obj U ≅ (sheafify J (K.X n)).obj U := by
  letI := hU n
  exact asIso ((toSheafify J (K.X n)).app U)

def complexIso :
    (((CategoryTheory.evaluation Cᵒᵖ D).obj U).mapHomologicalComplex c).obj K ≅
      (((sheafToPresheaf J D ⋙ (CategoryTheory.evaluation Cᵒᵖ D).obj U).mapHomologicalComplex c).obj
        (((presheafToSheaf J D).mapHomologicalComplex c).obj K)) :=
  HomologicalComplex.Hom.isoOfComponents
    (componentIso J c K U hU)
    (fun i j _ => (congrArg (fun α => α.app U) (toSheafify_naturality J (K.d i j))).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationSectionComplexIso.SheafificationSectionComplex
