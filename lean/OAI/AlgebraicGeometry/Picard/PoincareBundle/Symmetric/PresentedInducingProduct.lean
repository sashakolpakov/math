import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFiberContractionSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ExternalTensorPointSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FixedFiberPointSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedProductPresentation

/-! # Presented Inducing Product -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.PresentedInducingProduct

noncomputable section

/-! Matching Poincare frames turn the inducing-formula symmetry into the actual exchange of the two input fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedProductPresentation

theorem finish {C : Type*} [Category C] {A B D E F G Z : C}
    (r : A ≅ B) (r' : D ≅ E) (e : A ≅ F) (e' : D ≅ G)
    (a : A ≅ D) (b : B ≅ E) (c : F ≅ G) (t : F ≅ Z) (t' : G ≅ Z)
    (hr : a ≪≫ r' = r ≪≫ b) (he : e ≪≫ c = a ≪≫ e') (ht : c ≪≫ t' = t) :
    r.symm ≪≫ e ≪≫ t = b ≪≫ r'.symm ≪≫ e' ≪≫ t' := by
  have hf : (e ≪≫ t) ≪≫ Iso.refl Z = a ≪≫ (e' ≪≫ t') := by
    rw [Iso.trans_refl, ← ht, ← Iso.trans_assoc, he, Iso.trans_assoc]
  have hp := InducingFiberContractionSymmetry.changed_sources r r' (e ≪≫ t) (e' ≪≫ t')
    a b (Iso.refl Z) hr hf
  simpa only [Iso.trans_refl] using hp

variable {S : Scheme.{u}} {A : Over S} [GrpObj A] [IsCommMonObj A]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj Q.sheaf ≅ Q.sheaf)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])

/-- The presented product on exchanged coordinates is exactly the original product preceded by
the canonical tensor exchange; no scalar multiple is introduced. -/
theorem exchanged
    (he : (Scheme.Modules.pullback (β_ A A).hom.left).mapIso (InducingFormulaSymmetry.regrouped A Q L e) ≪≫ InducingFormulaSymmetry.targetSymmetry A L =
      InducingFormulaSymmetry.sourceSymmetry A Q L σ ≪≫ InducingFormulaSymmetry.regrouped A Q L e)
    {T : Over S} (q : T ⟶ A ⊗ A) (x y z : T ⟶ A)
    (hx : q ≫ fst A A = x) (hy : q ≫ snd A A = y) (hz : q ≫ μ[A] = z)
    (hx' : (q ≫ (β_ A A).hom) ≫ fst A A = y)
    (hy' : (q ≫ (β_ A A).hom) ≫ snd A A = x) (hz' : (q ≫ (β_ A A).hom) ≫ μ[A] = z)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared Q) (q ≫ (β_ A A).hom))
    (s' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared Q) q)
    (hs : s ≪≫ Line.SymmetryFibers.atPoint (Line.Comparison.Bundle.fromShared Q) (β_ A A).hom σ q = s') :
    FramedProductPresentation.presentation Q L e (q ≫ (β_ A A).hom) s y x z hx' hy' hz' =
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso (Line.Fibers.fiber L y) (Line.Fibers.fiber L x) ≪≫ FramedProductPresentation.presentation Q L e q s' x y z hx hy hz := by
  let a := Line.SymmetryFibers.atPoint (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A L)) (β_ A A).hom
    (ExternalTensorSymmetry.symmetry A L) q
  let c := Line.SymmetryFibers.atPoint (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.targetLine A L)) (β_ A A).hom (InducingFormulaSymmetry.targetSymmetry A L) q
  have hr := ExternalTensorPointSymmetry.atPoint A L q x y hx hy hx' hy'
  have ht := FixedFiberPointSymmetry.atPoint L (β_ A A).hom μ[A] (IsCommMonObj.mul_comm A) q z hz hz'
  have hmap : FramedProductPresentation.mapIso Q L e (q ≫ (β_ A A).hom) s ≪≫ c = a ≪≫ FramedProductPresentation.mapIso Q L e q s' := by
    apply Iso.ext
    exact InducingFiberContractionSymmetry.contraction_atPoint (Line.Comparison.Bundle.fromShared Q)
      (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.factorLine A L)) (Line.Comparison.Bundle.fromShared (InducingFormulaSymmetry.targetLine A L)) (β_ A A).hom (InducingFormulaSymmetry.regrouped A Q L e)
      σ (ExternalTensorSymmetry.symmetry A L) (InducingFormulaSymmetry.targetSymmetry A L) he q s s' hs
  exact finish (Tensor.FiberComposition.comparison L (fst A A) (snd A A) (q ≫ (β_ A A).hom) y x hx' hy')
    (Tensor.FiberComposition.comparison L (fst A A) (snd A A) q x y hx hy)
    (FramedProductPresentation.mapIso Q L e (q ≫ (β_ A A).hom) s) (FramedProductPresentation.mapIso Q L e q s') a (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso (Line.Fibers.fiber L y) (Line.Fibers.fiber L x)) c
    (Line.Fibers.fiberPullbackIso L (q ≫ (β_ A A).hom) μ[A] z hz') (Line.Fibers.fiberPullbackIso L q μ[A] z hz) hr hmap ht

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.PresentedInducingProduct
