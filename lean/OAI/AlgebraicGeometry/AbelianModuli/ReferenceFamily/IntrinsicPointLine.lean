import OAI.RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle
import OAI.RepresentationTheory.Theta.Geometric.ConstantPicardPullback
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicTranslation

/-! # Intrinsic Point Line -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPointLine

noncomputable section

section

/-! Actual complex fibers of an algebraic line-bundle family. These
identities use only tensor pullback and the group law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

def nativePointFamilyMap {A P : Over Foundations.Scheme.ProjectiveSpace.complexBase} (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) : A ⟶ P ⊗ A :=
  lift (Over.mkIdTerminal.from A ≫ p) (𝟙 A)

def nativePointFamilyLine {A P : Over Foundations.Scheme.ProjectiveSpace.complexBase} (Q : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) : HilbertConstruction.Line.Bundles.LineBundle A.left :=
  Q.pullback (nativePointFamilyMap (A := A) p).left

theorem nativePointFamilyMap_baseChange {A P R : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : P ⟶ R) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) :
    nativePointFamilyMap (A := A) p ≫ (f ⊗ₘ 𝟙 A) = nativePointFamilyMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [nativePointFamilyMap, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map]

theorem nativePointFamilyLine_baseChange {A P R : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (Q : HilbertConstruction.Line.Bundles.LineBundle (R ⊗ A).left) (f : P ⟶ R) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) :
    HilbertConstruction.Line.Bundles.LineBundle.classOf (nativePointFamilyLine (Q.pullback (f ⊗ₘ 𝟙 A).left) p) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (nativePointFamilyLine Q (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)) := by
  change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (nativePointFamilyMap (A := A) p).left
    (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (f ⊗ₘ 𝟙 A).left (HilbertConstruction.Line.Bundles.LineBundle.classOf Q)) = _
  rw [RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp]
  exact congrArg (fun h => RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback h (HilbertConstruction.Line.Bundles.LineBundle.classOf Q))
    (congrArg Over.Hom.left (nativePointFamilyMap_baseChange f p))

theorem nativePointFamilyLine_congr {A P : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (Q R : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left) (e : Q.sheaf ≅ R.sheaf) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) :
    HilbertConstruction.Line.Bundles.LineBundle.classOf (nativePointFamilyLine Q p) = HilbertConstruction.Line.Bundles.LineBundle.classOf (nativePointFamilyLine R p) :=
  Quotient.sound ⟨(Scheme.Modules.pullback (nativePointFamilyMap (A := A) p).left).mapIso e⟩

theorem nativePointDifference_class {d : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme d Foundations.Scheme.ProjectiveSpace.complexBase)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) :
    HilbertConstruction.Line.Bundles.LineBundle.classOf (nativePointFamilyLine (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle A L) p) =
      RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback ((𝟙 A.scheme) * (Over.mkIdTerminal.from A.scheme ≫ p)).left
        (HilbertConstruction.Line.Bundles.LineBundle.classOf L) * (HilbertConstruction.Line.Bundles.LineBundle.classOf L)⁻¹ := by
  have H := RepresentationTheory.Theta.Geometric.Picard.PicardPullback.algebraicDifferenceBundle_pullback_class L (fst A.scheme A.scheme).left
    (snd A.scheme A.scheme).left μ[A.scheme].left (nativePointFamilyMap p).left
  have hmul : nativePointFamilyMap p ≫ μ[A.scheme] =
      (𝟙 A.scheme) * (Over.mkIdTerminal.from A.scheme ≫ p) := mul_comm _ _
  have hfst : nativePointFamilyMap p ≫ fst A.scheme A.scheme = Over.mkIdTerminal.from A.scheme ≫ p :=
    lift_fst _ _
  have hsnd : nativePointFamilyMap p ≫ snd A.scheme A.scheme = 𝟙 A.scheme := lift_snd _ _
  rw [show (nativePointFamilyMap p).left ≫ μ[A.scheme].left =
      ((𝟙 A.scheme) * (Over.mkIdTerminal.from A.scheme ≫ p)).left from congrArg Over.Hom.left hmul,
    show (nativePointFamilyMap p).left ≫ (fst A.scheme A.scheme).left =
      (Over.mkIdTerminal.from A.scheme).left ≫ p.left from congrArg Over.Hom.left hfst,
    show (nativePointFamilyMap p).left ≫ (snd A.scheme A.scheme).left = 𝟙 A.scheme.left from
      congrArg Over.Hom.left hsnd,
    RepresentationTheory.Theta.Geometric.ConstantPicardPullback.picardPullback_constant ℂ, inv_one, mul_one, RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_id] at H
  exact H

end

/-! Fixing the terminal complex parameter identifies its product
family with the original scheme, retaining the actual pullback maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

def nativePointUnitIso (A : Over Foundations.Scheme.ProjectiveSpace.complexBase) : A ≅ Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⊗ A where
  hom := nativePointFamilyMap (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))
  inv := snd (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) A
  hom_inv_id := lift_snd _ _
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.mkIdTerminal.hom_ext _ _
    · simp only [nativePointFamilyMap, Category.assoc, lift_snd, Category.comp_id, Category.id_comp]

theorem nativePointUnit_class_recovery (A : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⊗ A).left) :
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) A).left
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (nativePointUnitIso A).hom.left q) = q := by
  have he := congrArg Over.Hom.left (nativePointUnitIso A).inv_hom_id
  exact (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp _ _ q).trans
    ((congrArg (fun f => RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback f q) he).trans (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_id q))

theorem nativePointFamilyLine_parameter_pullback {A P : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (Q : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) :
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (nativePointUnitIso A).hom.left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (x ⊗ₘ 𝟙 A).left)) =
        HilbertConstruction.Line.Bundles.LineBundle.classOf (nativePointFamilyLine Q x) := by
  have he := nativePointFamilyMap_baseChange (A := A) x (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map x (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) = x := Category.id_comp x
  rw [hx] at he
  exact (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp _ _ (HilbertConstruction.Line.Bundles.LineBundle.classOf Q)).trans
    (congrArg (fun f => RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback f (HilbertConstruction.Line.Bundles.LineBundle.classOf Q)) (congrArg Over.Hom.left he))

theorem nativePointFamilyLine_constant_recovery {A P : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (Q : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) :
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) A).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf (nativePointFamilyLine Q x)) =
        HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (x ⊗ₘ 𝟙 A).left) :=
  (congrArg (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) A).left)
    (nativePointFamilyLine_parameter_pullback Q x).symm).trans
      (nativePointUnit_class_recovery A (HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (x ⊗ₘ 𝟙 A).left)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPointLine
