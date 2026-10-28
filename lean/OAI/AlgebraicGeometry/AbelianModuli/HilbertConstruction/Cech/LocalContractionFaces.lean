/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafLocalContraction.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.LocalContractionSections

/-! # Local Contraction Faces -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.LocalContractionFaces.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}} {ι : Type u}
variable (U : ι → Opens X)
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)

theorem cechFaceSection_zero_transport {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (n : ℕ)
    (s : (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).obj.obj (op V)) (i : Fin (n + 2) → ι) :
    F.obj.map (eqToHom (congrArg op
        (LocalContractionIndices.IntrinsicCech.cechPrependIntersection_eq U i₀ hV i)))
        (LocalContractionSections.IntrinsicCech.cechFaceSection U F (n + 1) V s 0 (LocalContractionIndices.IntrinsicCech.cechPrependIndex i₀ i)) =
      IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U (n + 1) V s i := by
  rw [LocalContractionSections.IntrinsicCech.cechFaceSection]
  rw [← LocalContractionSections.IntrinsicCech.cechTermSectionsAddEquiv_transport U F (n + 1) V s
    (LocalContractionIndices.IntrinsicCech.cechPrependDeleteZero i₀ i)]
  change (F.obj.map _ ≫ F.obj.map _) _ = F.obj.map _ _
  exact ConcreteCategory.congr_hom
    ((F.obj.map_comp _ _).symm.trans
      (congrArg F.obj.map (Subsingleton.elim _ _))) _

theorem cechFaceSection_succ_transport {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (n : ℕ)
    (s : (IntrinsicCech.SheafTerms.cechTerm F U (n + 1)).obj.obj (op V)) (i : Fin (n + 2) → ι)
    (k : Fin (n + 2)) :
    F.obj.map (eqToHom (congrArg op
        (LocalContractionIndices.IntrinsicCech.cechPrependIntersection_eq U i₀ hV i)))
        (LocalContractionSections.IntrinsicCech.cechFaceSection U F (n + 1) V s k.succ (LocalContractionIndices.IntrinsicCech.cechPrependIndex i₀ i)) =
      LocalContractionSections.IntrinsicCech.cechFaceSection U F n V (LocalContractionSections.IntrinsicCech.cechLocalContraction U F i₀ hV n s) k i := by
  rw [LocalContractionSections.IntrinsicCech.cechFaceSection, LocalContractionSections.IntrinsicCech.cechFaceSection, LocalContractionSections.IntrinsicCech.cechLocalContraction_apply]
  erw [← LocalContractionSections.IntrinsicCech.cechTermSectionsAddEquiv_transport U F (n + 1) V s
    (LocalContractionIndices.IntrinsicCech.cechPrependDeleteSucc i₀ i k)]
  change (F.obj.map _ ≫ F.obj.map _) _ =
    (F.obj.map _ ≫ F.obj.map _ ≫ F.obj.map _) _
  exact ConcreteCategory.congr_hom
    ((F.obj.map_comp _ _).symm.trans
      ((congrArg F.obj.map (Subsingleton.elim _ _)).trans
        ((F.obj.map_comp _ _).trans
          (congrArg (fun f ↦ F.obj.map _ ≫ f) (F.obj.map_comp _ _))))) _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.LocalContractionFaces.IntrinsicCech
