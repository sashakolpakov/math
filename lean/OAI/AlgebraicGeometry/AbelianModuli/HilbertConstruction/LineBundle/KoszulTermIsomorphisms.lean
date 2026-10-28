import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulComplex

/-! # Koszul Term Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.KoszulTermIsomorphisms

noncomputable section

/-! Isomorphisms of Koszul terms under coefficient isomorphisms and tensoring by the defining line bundle. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

local instance e33KoszulTermTensorAdditive {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) :
    (TensorEquivalence.lineBundleTensorEquivalence L).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

def lineBundleSectionKoszulStep_XIsoBiprod {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (C : CochainComplex X.Modules ℤ) (i : ℤ) :
    (SectionKoszulStep.lineBundleSectionKoszulStep L s C).X i ≅
      C.X (i + 1) ⊞ (TensorEquivalence.lineBundleTensorEquivalence L).functor.obj (C.X i) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (SectionKoszulStep.lineBundleSectionComplexMap L s C)
    i (i + 1) rfl

def lineBundleKoszul_coefficientTermIso {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    {M N : X.Modules} (e : M ≅ N) (ss : List (Line.Bundles.structureModule X ⟶ L.sheaf)) (i : ℤ) :
    (SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss).X i ≅
      (SectionKoszulComplex.lineBundleSectionKoszulComplex L N ss).X i := by
  induction ss generalizing i with
  | nil =>
    exact (HomologicalComplex.eval X.Modules (.up ℤ) i).mapIso
      ((HomologicalComplex.single X.Modules (.up ℤ) 0).mapIso e)
  | cons s ss ih =>
    exact lineBundleSectionKoszulStep_XIsoBiprod L s _ i ≪≫
      biprod.mapIso (ih (i + 1)) ((TensorEquivalence.lineBundleTensorEquivalence L).functor.mapIso (ih i)) ≪≫
      (lineBundleSectionKoszulStep_XIsoBiprod L s _ i).symm

def lineBundleKoszul_tensorTermIso {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (M : X.Modules) (ss : List (Line.Bundles.structureModule X ⟶ L.sheaf)) (i : ℤ) :
    (TensorEquivalence.lineBundleTensorEquivalence L).functor.obj ((SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss).X i) ≅
      (SectionKoszulComplex.lineBundleSectionKoszulComplex L ((TensorEquivalence.lineBundleTensorEquivalence L).functor.obj M) ss).X i := by
  let F := (TensorEquivalence.lineBundleTensorEquivalence L).functor
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryProducts F
  induction ss generalizing i with
  | nil =>
    by_cases hi : i = 0
    · subst i
      simpa only [SectionKoszulComplex.lineBundleSectionKoszulComplex, HomologicalComplex.single_obj_X_self] using
        (Iso.refl (F.obj M))
    · exact (Functor.map_isZero F (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)).iso
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (F.obj M) i hi)
  | cons s ss ih =>
    let C := SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss
    exact F.mapIso (lineBundleSectionKoszulStep_XIsoBiprod L s C i) ≪≫
      F.mapBiprod (C.X (i + 1)) (F.obj (C.X i)) ≪≫
      biprod.mapIso (ih (i + 1)) (F.mapIso (ih i)) ≪≫
      (lineBundleSectionKoszulStep_XIsoBiprod L s _ i).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.KoszulTermIsomorphisms
