import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.LineProducts

/-! # Vertical Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.VerticalProducts.Construction

noncomputable section

/-! The same universal-coordinate construction for multiplication in
the second factor, retaining the original order of the line's factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

variable {S : Scheme.{u}} {A X : Over S}

def verticalInputLeft : (A ⊗ A) ⊗ X ⟶ X ⊗ A :=
  lift (snd (A ⊗ A) X) (fst (A ⊗ A) X ≫ fst A A)

def verticalInputRight : (A ⊗ A) ⊗ X ⟶ X ⊗ A :=
  lift (snd (A ⊗ A) X) (fst (A ⊗ A) X ≫ snd A A)

def verticalProductParameterLift {T : Over S} (a b : T ⟶ X ⊗ A) : T ⟶ (A ⊗ A) ⊗ X :=
  lift (lift (a ≫ snd X A) (b ≫ snd X A)) (a ≫ fst X A)

theorem verticalProductParameterLift_left {T : Over S} (a b : T ⟶ X ⊗ A) :
    verticalProductParameterLift a b ≫ verticalInputLeft = a := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [verticalProductParameterLift, verticalInputLeft, Category.assoc, lift_fst, lift_snd, lift_fst_assoc]

theorem verticalProductParameterLift_right {T : Over S} (a b : T ⟶ X ⊗ A)
    (h : a ≫ fst X A = b ≫ fst X A) :
    verticalProductParameterLift a b ≫ verticalInputRight = b := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [verticalProductParameterLift, verticalInputRight, Category.assoc, lift_fst, lift_snd] using h
  · simp only [verticalProductParameterLift, verticalInputRight, Category.assoc, lift_snd, lift_fst_assoc]

theorem verticalProductParameterLift_natural {T U : Over S} (r : U ⟶ T)
    (a b : T ⟶ X ⊗ A) (a' b' : U ⟶ X ⊗ A) (ha : r ≫ a = a') (hb : r ≫ b = b') :
    r ≫ verticalProductParameterLift a b = verticalProductParameterLift a' b' := by
  simp only [verticalProductParameterLift, comp_lift, ← Category.assoc, ha, hb]

variable [GrpObj A]

def verticalOutputPoint : (A ⊗ A) ⊗ X ⟶ X ⊗ A :=
  lift (snd (A ⊗ A) X) ((fst (A ⊗ A) X ≫ fst A A) * (fst (A ⊗ A) X ≫ snd A A))

theorem verticalProductParameterLift_output {T : Over S} (a b c : T ⟶ X ⊗ A)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd X A) (fst X A) a b c) :
    verticalProductParameterLift a b ≫ verticalOutputPoint = c := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [verticalProductParameterLift, verticalOutputPoint, Category.assoc, lift_fst, lift_snd] using h.2.2
  · simpa only [verticalProductParameterLift, verticalOutputPoint, Category.assoc, lift_fst, lift_snd,
      lift_fst_assoc, MonObj.comp_mul] using h.1

variable (L : Picard.PoincareBundle.Line.Bundles.LineBundle (X ⊗ A).left)
  (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L verticalInputLeft) (Picard.PoincareBundle.Line.Fibers.fiber L verticalInputRight) (Picard.PoincareBundle.Line.Fibers.fiber L verticalOutputPoint))

def verticalProductFromUniversal {T : Over S} (a c d : T ⟶ X ⊗ A) (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd X A) (fst X A) a c d) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L a) (Picard.PoincareBundle.Line.Fibers.fiber L c) (Picard.PoincareBundle.Line.Fibers.fiber L d) :=
  Picard.PoincareBundle.Line.Fibers.pullBilinear L (verticalProductParameterLift a c) verticalInputLeft verticalInputRight verticalOutputPoint a c d
    (verticalProductParameterLift_left a c) (verticalProductParameterLift_right a c h.2.1)
    (verticalProductParameterLift_output a c d h) b

instance verticalProductFromUniversal_isIso [IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b)]
    {T : Over S} (a c d : T ⟶ X ⊗ A) (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd X A) (fst X A) a c d) :
    IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom (verticalProductFromUniversal L b a c d h)) := by
  unfold verticalProductFromUniversal Picard.PoincareBundle.Line.Fibers.pullBilinear
  rw [Picard.PoincareBundle.Bilinear.Transport.toHom_transport, Picard.PoincareBundle.Bilinear.BilinearPullback.toHom_pullback]
  unfold Picard.PoincareBundle.Bilinear.BilinearPullback.pulledHom
  infer_instance

theorem verticalProductFromUniversal_natural {T U : Over S} (r : U ⟶ T)
    (a c d : T ⟶ X ⊗ A) (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd X A) (fst X A) a c d)
    (a' c' d' : U ⟶ X ⊗ A) (h' : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd X A) (fst X A) a' c' d')
    (ha : r ≫ a = a') (hc : r ≫ c = c') (hd : r ≫ d = d') :
    Picard.PoincareBundle.Line.Fibers.pullBilinear L r a c d a' c' d' ha hc hd (verticalProductFromUniversal L b a c d h) =
      verticalProductFromUniversal L b a' c' d' h' := by
  have hp := verticalProductParameterLift_natural r a c a' c' ha hc
  have hleft : (r ≫ verticalProductParameterLift a c) ≫ verticalInputLeft = a' := by
    rw [Category.assoc, verticalProductParameterLift_left, ha]
  have hright : (r ≫ verticalProductParameterLift a c) ≫ verticalInputRight = c' := by
    rw [Category.assoc, verticalProductParameterLift_right a c h.2.1, hc]
  have hout : (r ≫ verticalProductParameterLift a c) ≫ verticalOutputPoint = d' := by
    rw [Category.assoc, verticalProductParameterLift_output a c d h, hd]
  exact (Picard.PoincareBundle.FiberBilinearComposition.pullBilinear_comp L (verticalProductParameterLift a c) r
    verticalInputLeft verticalInputRight verticalOutputPoint a c d a' c' d'
    (verticalProductParameterLift_left a c) (verticalProductParameterLift_right a c h.2.1)
    (verticalProductParameterLift_output a c d h) ha hc hd hleft hright hout b).trans
    (LineProducts.Construction.pullBilinear_congr_parameter L _ _ hp _ _ _ _ _ _ hleft hright hout
      (verticalProductParameterLift_left a' c') (verticalProductParameterLift_right a' c' h'.2.1)
      (verticalProductParameterLift_output a' c' d' h') b)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.VerticalProducts.Construction
