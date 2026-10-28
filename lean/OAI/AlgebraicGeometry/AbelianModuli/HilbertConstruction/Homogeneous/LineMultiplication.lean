import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceClassBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.PointTranslations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointLineBundleTriviality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ExternalTensorBundle

/-! # Line Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.LineMultiplication

noncomputable section

/-! An actual homogeneous line over a field satisfies the multiplication
formula, independently of any chosen dual abelian variety. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {K : Type} [Field K] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf L))

private theorem homogeneousLine_difference_formula {S : Scheme}
    (X : Over S) [GrpObj X] (q : Line.Bundles.LineBundle.IsoClass X.left)
    {T : Over S} (a b : T ⟶ X) :
    RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass X q a b =
      RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (a * b).left q * (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback a.left q)⁻¹ *
        (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback b.left q)⁻¹ := by
  have h57 (r : Line.Bundles.LineBundle.IsoClass T.left) : Picard.Homomorphisms.LineBundleDual.Construction.dualLineBundleClass r = r⁻¹ :=
    eq_inv_of_mul_eq_one_left (Picard.Homomorphisms.LineBundleEvaluation.Construction.tensorClass_dual r)
  dsimp only [RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass]
  exact congrArg₂ (fun x y : Line.Bundles.LineBundle.IsoClass T.left => RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (a * b).left q * x * y)
    (h57 (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback a.left q)) (h57 (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback b.left q))

include hL in
theorem homogeneousLine_mul_class {T : Over (Spec (.of K))} (a b : T ⟶ A.scheme) :
    Line.Bundles.LineBundle.classOf (L.pullback (a * b).left) =
      Line.Bundles.LineBundle.classOf ((L.pullback a.left).tensor (L.pullback b.left)) := by
  have h := Picard.ThetaConstruction.DifferenceClassBaseChange.Geometric.homogeneousLine_groupDifference A L hL a b
  rw [homogeneousLine_difference_formula] at h
  rw [Line.Bundles.LineBundle.classOf_tensor]
  change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (a * b).left (Line.Bundles.LineBundle.classOf L) =
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback a.left (Line.Bundles.LineBundle.classOf L) * RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback b.left (Line.Bundles.LineBundle.classOf L)
  apply mul_inv_eq_one.mp
  simpa only [mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h

def homogeneousLine_mulIso {T : Over (Spec (.of K))} (a b : T ⟶ A.scheme) :
    (L.pullback (a * b).left).sheaf ≅
      ((L.pullback a.left).tensor (L.pullback b.left)).sheaf :=
  Classical.choice (Quotient.exact (homogeneousLine_mul_class A L hL a b))

def lineBundle_constantPointIso (a : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) :
    (L.pullback (toUnit A.scheme ≫ a).left).sheaf ≅ Line.Bundles.structureModule A.scheme.left := by
  have : Subsingleton ((𝟙_ (Over (Spec (.of K)))).left) :=
    inferInstanceAs (Subsingleton (Spec (.of K)))
  have : Nonempty ((𝟙_ (Over (Spec (.of K)))).left) :=
    inferInstanceAs (Nonempty (Spec (.of K)))
  exact ((Scheme.Modules.pullbackComp (toUnit A.scheme).left a.left).app L.sheaf).symm ≪≫
    (Scheme.Modules.pullback (toUnit A.scheme).left).mapIso
      (L.pullback a.left).trivialization_of_subsingleton ≪≫
    Line.Bundles.structureModulePullbackIso (toUnit A.scheme).left

def homogeneousLine_translationIso (a : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) :
    (L.pullback (A.basePointTranslation a).left).sheaf ≅ L.sheaf :=
  homogeneousLine_mulIso A L hL (toUnit A.scheme ≫ a) (𝟙 A.scheme) ≪≫
    Tensor.ProductSheaf.tensorModuleCongr (lineBundle_constantPointIso A L a)
      ((Scheme.Modules.pullbackId A.scheme.left).app L.sheaf) ≪≫
    Tensor.ProductSheaf.tensorModuleUnitLeftIso L.sheaf

def homogeneousLine_inversePairingIso :
    (L.tensor (L.pullback ((𝟙 A.scheme)⁻¹).left)).sheaf ≅ Line.Bundles.structureModule A.scheme.left := by
  have e : (L.pullback (1 : A.scheme ⟶ A.scheme).left).sheaf ≅
      ((L.pullback (𝟙 A.scheme : A.scheme ⟶ A.scheme).left).tensor
        (L.pullback ((𝟙 A.scheme)⁻¹).left)).sheaf := by
    simpa only [mul_inv_cancel] using
      homogeneousLine_mulIso A L hL (𝟙 A.scheme) ((𝟙 A.scheme)⁻¹)
  exact Tensor.ProductSheaf.tensorModuleCongr ((Scheme.Modules.pullbackId A.scheme.left).symm.app L.sheaf)
    (Iso.refl _) ≪≫ e.symm ≪≫ lineBundle_constantPointIso A L η[A.scheme]

def homogeneousLine_additionIso :
    (L.pullback (fst A.scheme A.scheme * snd A.scheme A.scheme).left).sheaf ≅
      (Graph.ExternalTensorBundle.externalTensorBundle (A := A.scheme) (B := A.scheme) L L).sheaf :=
  homogeneousLine_mulIso A L hL (fst A.scheme A.scheme) (snd A.scheme A.scheme)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.LineMultiplication
