import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedSubgroupInducingProduct
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedTensorContraction

/-! # Framed Subgroup Fiber Products -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedSubgroupFiberProducts

noncomputable section

/-! The subgroup inducing product and its actual translations on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport
open OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedSubgroupInducingProduct

theorem first_pair {S : Scheme.{u}} {H A T : Over S} (i : H ⟶ A) (a : T ⟶ H) (x : T ⟶ A) :
    lift a x ≫ (fst H A ≫ i) = a ≫ i := by rw [← Category.assoc, lift_fst]

variable {S : Scheme.{u}} {H A : Over S} [GrpObj A] (i : H ⟶ A)
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf)

/-- The global product at a subgroup element and a starting point. -/
def globalProduct : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L (fst H A ≫ i)) (Line.Fibers.fiber L (snd H A)) (Line.Fibers.fiber L (NormalizedKernelTranslation.action i)) :=
  AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (FramedSubgroupInducingProduct.productIso i Q L e s).hom

/-- Evaluate the actual global product through the three geometric fiber identifications. -/
def atPoint {T : Over S} (a : T ⟶ H) (x y : T ⟶ A) (h : (a ≫ i) * x = y) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L (a ≫ i)) (Line.Fibers.fiber L x) (Line.Fibers.fiber L y) :=
  Bilinear.Transport.transport (Bilinear.BilinearPullback.pullback (lift a x).left (Line.Fibers.fiber_isLine L (fst H A ≫ i)) (Line.Fibers.fiber_isLine L (snd H A))
    (globalProduct i Q L e s))
    (Line.Fibers.fiberPullbackIso L (lift a x) (fst H A ≫ i) (a ≫ i) (first_pair i a x))
    (Line.Fibers.fiberPullbackIso L (lift a x) (snd H A) x (lift_snd a x))
    (Line.Fibers.fiberPullbackIso L (lift a x) (NormalizedKernelTranslation.action i) y ((Subgroup.TranslationFibers.action_pair i a x).trans h))

variable (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule H.left ≅ Line.Fibers.fiber L i)

/-- The global translation is the contraction of this actual product by the subgroup-line frame. -/
theorem translation_hom :
    (FramedSubgroupInducingProduct.translationIso i Q L e s t).hom =
      Bilinear.Contraction.contractLeft (globalProduct i Q L e s)
        (GlobalPullbackFrame.atPoint i L t (fst H A) (fst H A ≫ i) rfl).hom :=
  FramedTensorContraction.hom_eq (FramedSubgroupInducingProduct.productIso i Q L e s)
    (GlobalPullbackFrame.atPoint i L t (fst H A) (fst H A ≫ i) rfl)

/-- Fiber transport of the constructed global translation inserts exactly the frame at the
subgroup-valued point, including on nonreduced test schemes. -/
theorem transport_contraction {T : Over S} (a : T ⟶ H) (x y : T ⟶ A) (h : (a ≫ i) * x = y) :
    (Subgroup.TranslationFibers.transportIso i L (FramedSubgroupInducingProduct.translationIso i Q L e s t) x y a h).hom =
      Bilinear.Contraction.contractLeft (atPoint i Q L e s a x y h)
        (GlobalPullbackFrame.atPoint i L t a (a ≫ i) rfl).hom := by
  let st := GlobalPullbackFrame.atPoint i L t (fst H A) (fst H A ≫ i) rfl
  let sa := GlobalPullbackFrame.atPoint i L t a (a ≫ i) rfl
  let ca := Line.Fibers.fiberPullbackIso L (lift a x) (fst H A ≫ i) (a ≫ i) (first_pair i a x)
  let cx := Line.Fibers.fiberPullbackIso L (lift a x) (snd H A) x (lift_snd a x)
  let cy := Line.Fibers.fiberPullbackIso L (lift a x) (NormalizedKernelTranslation.action i) y ((Subgroup.TranslationFibers.action_pair i a x).trans h)
  have hf := GlobalFrameNaturality.atPoint_pullback i L t (lift a x) (fst H A) (fst H A ≫ i) rfl
    a (a ≫ i) rfl (lift_fst a x) (first_pair i a x)
  have hs : Bilinear.ContractionPullback.pulledSection (lift a x).left st.hom ≫ ca.hom = sa.hom := congrArg Iso.hom hf
  have hp := Bilinear.Transport.contractLeft_pullback_transport (lift a x).left (Line.Fibers.fiber_isLine L (fst H A ≫ i))
    (Line.Fibers.fiber_isLine L (snd H A)) (globalProduct i Q L e s) ca cx cy st.hom
  have he : Bilinear.Contraction.contractLeft (atPoint i Q L e s a x y h) sa.hom =
      cx.inv ≫ (Scheme.Modules.pullback (lift a x).left).map
        (Bilinear.Contraction.contractLeft (globalProduct i Q L e s) st.hom) ≫ cy.hom :=
    (congrArg (Bilinear.Contraction.contractLeft (atPoint i Q L e s a x y h)) hs).symm.trans hp
  have ht := congrArg (fun z => cx.inv ≫ (Scheme.Modules.pullback (lift a x).left).map z ≫ cy.hom)
    (translation_hom i Q L e s t)
  exact ht.trans he.symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedSubgroupFiberProducts
