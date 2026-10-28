import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberBilinearComposition

/-! # Line Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.LineProducts.Construction

noncomputable section

/-! A genuine product map on the universal parameter scheme gives
its invertible, natural bilinear operation on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes

universe u

variable {S : Scheme.{u}} {A X : Over S}

def lineProductParameterLift {T : Over S} (a b : T ⟶ A ⊗ X) : T ⟶ (A ⊗ A) ⊗ X :=
  lift (lift (a ≫ fst A X) (b ≫ fst A X)) (a ≫ snd A X)

theorem lineProductParameterLift_left {T : Over S} (a b : T ⟶ A ⊗ X) :
    lineProductParameterLift a b ≫ Picard.PoincareBundle.Product.ParameterSchemes.inputLeft A X = a := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [lineProductParameterLift, Picard.PoincareBundle.Product.ParameterSchemes.inputLeft, Category.assoc, lift_fst, lift_snd, lift_fst_assoc]

theorem lineProductParameterLift_right {T : Over S} (a b : T ⟶ A ⊗ X)
    (h : a ≫ snd A X = b ≫ snd A X) :
    lineProductParameterLift a b ≫ Picard.PoincareBundle.Product.ParameterSchemes.inputRight A X = b := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [lineProductParameterLift, Picard.PoincareBundle.Product.ParameterSchemes.inputRight, Category.assoc, lift_fst, lift_snd, lift_fst_assoc]
  · simpa only [lineProductParameterLift, Picard.PoincareBundle.Product.ParameterSchemes.inputRight, Category.assoc, lift_fst, lift_snd, lift_fst_assoc] using h

variable [GrpObj A]

theorem lineProductParameterLift_output {T : Over S} (a b c : T ⟶ A ⊗ X)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a b c) :
    lineProductParameterLift a b ≫ Picard.PoincareBundle.Product.ParameterSchemes.outputPoint A X = c := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [lineProductParameterLift, Picard.PoincareBundle.Product.ParameterSchemes.outputPoint, Category.assoc, lift_fst, lift_snd, lift_fst_assoc,
      MonObj.comp_mul] using h.1
  · simpa only [lineProductParameterLift, Picard.PoincareBundle.Product.ParameterSchemes.outputPoint, Category.assoc, lift_fst, lift_snd] using h.2.2

omit [GrpObj A] in
theorem lineProductParameterLift_natural {T U : Over S} (r : U ⟶ T)
    (a b : T ⟶ A ⊗ X) (a' b' : U ⟶ A ⊗ X) (ha : r ≫ a = a') (hb : r ≫ b = b') :
    r ≫ lineProductParameterLift a b = lineProductParameterLift a' b' := by
  simp only [lineProductParameterLift, comp_lift, ← Category.assoc, ha, hb]

theorem pullBilinear_congr_parameter {E P Q : Over S} (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left)
    (f g : Q ⟶ P) (hfg : f = g) (x y z : P ⟶ E) (x' y' z' : Q ⟶ E)
    (hx : f ≫ x = x') (hy : f ≫ y = y') (hz : f ≫ z = z')
    (hx' : g ≫ x = x') (hy' : g ≫ y = y') (hz' : g ≫ z = z')
    (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L y) (Picard.PoincareBundle.Line.Fibers.fiber L z)) :
    Picard.PoincareBundle.Line.Fibers.pullBilinear L f x y z x' y' z' hx hy hz b = Picard.PoincareBundle.Line.Fibers.pullBilinear L g x y z x' y' z' hx' hy' hz' b := by
  subst g
  rfl

variable (L : Picard.PoincareBundle.Line.Bundles.LineBundle (A ⊗ X).left)
  (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft A X)) (Picard.PoincareBundle.Line.Fibers.fiber L (Picard.PoincareBundle.Product.ParameterSchemes.inputRight A X)) (Picard.PoincareBundle.Line.Fibers.fiber L (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint A X)))

def lineProductFromUniversal {T : Over S} (a c d : T ⟶ A ⊗ X) (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a c d) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L a) (Picard.PoincareBundle.Line.Fibers.fiber L c) (Picard.PoincareBundle.Line.Fibers.fiber L d) :=
  Picard.PoincareBundle.Line.Fibers.pullBilinear L (lineProductParameterLift a c) (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft A X) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight A X) (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint A X) a c d
    (lineProductParameterLift_left a c) (lineProductParameterLift_right a c h.2.1)
    (lineProductParameterLift_output a c d h) b

instance lineProductFromUniversal_isIso [IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b)]
    {T : Over S} (a c d : T ⟶ A ⊗ X) (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a c d) :
    IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (lineProductFromUniversal L b a c d h)) := by
  unfold lineProductFromUniversal Picard.PoincareBundle.Line.Fibers.pullBilinear
  rw [Picard.PoincareBundle.Bilinear.Transport.toHom_transport, Picard.PoincareBundle.Bilinear.BilinearPullback.toHom_pullback]
  unfold Picard.PoincareBundle.Bilinear.BilinearPullback.pulledHom
  infer_instance

theorem lineProductFromUniversal_natural {T U : Over S} (r : U ⟶ T)
    (a c d : T ⟶ A ⊗ X) (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a c d)
    (a' c' d' : U ⟶ A ⊗ X) (h' : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a' c' d')
    (ha : r ≫ a = a') (hc : r ≫ c = c') (hd : r ≫ d = d') :
    Picard.PoincareBundle.Line.Fibers.pullBilinear L r a c d a' c' d' ha hc hd (lineProductFromUniversal L b a c d h) =
      lineProductFromUniversal L b a' c' d' h' := by
  have hp := lineProductParameterLift_natural r a c a' c' ha hc
  have hleft : (r ≫ lineProductParameterLift a c) ≫ Picard.PoincareBundle.Product.ParameterSchemes.inputLeft A X = a' := by
    rw [Category.assoc, lineProductParameterLift_left, ha]
  have hright : (r ≫ lineProductParameterLift a c) ≫ Picard.PoincareBundle.Product.ParameterSchemes.inputRight A X = c' := by
    rw [Category.assoc, lineProductParameterLift_right a c h.2.1, hc]
  have hout : (r ≫ lineProductParameterLift a c) ≫ Picard.PoincareBundle.Product.ParameterSchemes.outputPoint A X = d' := by
    rw [Category.assoc, lineProductParameterLift_output a c d h, hd]
  exact (Picard.PoincareBundle.FiberBilinearComposition.pullBilinear_comp L (lineProductParameterLift a c) r
    (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft A X) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight A X) (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint A X) a c d a' c' d'
    (lineProductParameterLift_left a c) (lineProductParameterLift_right a c h.2.1)
    (lineProductParameterLift_output a c d h) ha hc hd hleft hright hout b).trans
    (pullBilinear_congr_parameter L _ _ hp _ _ _ _ _ _ hleft hright hout
      (lineProductParameterLift_left a' c') (lineProductParameterLift_right a' c' h'.2.1)
      (lineProductParameterLift_output a' c' d' h') b)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.LineProducts.Construction
