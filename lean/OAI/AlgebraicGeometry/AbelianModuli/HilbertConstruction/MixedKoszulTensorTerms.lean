import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundleKoszulComplex

/-! # Mixed Koszul Tensor Terms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulTensorTerms

noncomputable section

/-! Tensoring the terms of a mixed Koszul complex by any line bundle
commutes with forming those terms. The comparison uses the actual
associator and symmetry of the module-sheaf tensor product. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory
universe u
local instance mixedKoszulModulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Module.SheafMonoidal.moduleMonoidalCategory X
local instance mixedKoszulModulesSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Module.SheafMonoidal.moduleSymmetricCategory X
local instance mixedKoszulTensorAdditive {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) :
    (LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

def lineBundleTensor_interchange {X : Scheme.{u}} (L H : Line.Bundles.LineBundle X) (M : X.Modules) :
    (LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.obj
      ((LineBundle.TensorEquivalence.lineBundleTensorEquivalence H).functor.obj M) ≅
    (LineBundle.TensorEquivalence.lineBundleTensorEquivalence H).functor.obj
      ((LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.obj M) :=
  (α_ L.sheaf H.sheaf M).symm ≪≫ tensorIso (β_ L.sheaf H.sheaf) (Iso.refl M) ≪≫
    (α_ H.sheaf L.sheaf M)

def mixedKoszul_coefficientTermIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (bs : List (LineBundleKoszulComplex.LineBundleSection X)) (i : ℤ) :
    (LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs).X i ≅ (LineBundleKoszulComplex.mixedLineBundleKoszulComplex N bs).X i := by
  induction bs generalizing i with
  | nil =>
    exact (HomologicalComplex.eval X.Modules (.up ℤ) i).mapIso
      ((HomologicalComplex.single X.Modules (.up ℤ) 0).mapIso e)
  | cons b bs ih =>
    exact LineBundle.KoszulTermIsomorphisms.lineBundleSectionKoszulStep_XIsoBiprod b.1 b.2 _ i ≪≫
      biprod.mapIso (ih (i + 1)) ((LineBundle.TensorEquivalence.lineBundleTensorEquivalence b.1).functor.mapIso (ih i)) ≪≫
      (LineBundle.KoszulTermIsomorphisms.lineBundleSectionKoszulStep_XIsoBiprod b.1 b.2 _ i).symm

def mixedKoszul_tensorTermIso {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) (M : X.Modules)
    (bs : List (LineBundleKoszulComplex.LineBundleSection X)) (i : ℤ) :
    (LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.obj ((LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs).X i) ≅
      (LineBundleKoszulComplex.mixedLineBundleKoszulComplex ((LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.obj M) bs).X i := by
  let F := (LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryProducts F
  induction bs generalizing i with
  | nil =>
    by_cases hi : i = 0
    · subst i
      simpa only [LineBundleKoszulComplex.mixedLineBundleKoszulComplex, HomologicalComplex.single_obj_X_self] using
        (Iso.refl (F.obj M))
    · exact (Functor.map_isZero F (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)).iso
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (F.obj M) i hi)
  | cons b bs ih =>
    let C := LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs
    let G := (LineBundle.TensorEquivalence.lineBundleTensorEquivalence b.1).functor
    exact F.mapIso (LineBundle.KoszulTermIsomorphisms.lineBundleSectionKoszulStep_XIsoBiprod b.1 b.2 C i) ≪≫
      F.mapBiprod (C.X (i + 1)) (G.obj (C.X i)) ≪≫
      biprod.mapIso (ih (i + 1))
        (lineBundleTensor_interchange L b.1 (C.X i) ≪≫ G.mapIso (ih i)) ≪≫
      (LineBundle.KoszulTermIsomorphisms.lineBundleSectionKoszulStep_XIsoBiprod b.1 b.2 _ i).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulTensorTerms
