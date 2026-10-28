import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Section Fibers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.SectionFibers

noncomputable section

/-! Inserting a section in one factor identifies the corresponding fiber of a fiber product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}}

def productRightFiberInclusion (p : X ⟶ S) (q : Y ⟶ S) (y : S ⟶ Y) (hy : y ≫ q = 𝟙 _) :
    X ⟶ pullback p q :=
  pullback.lift (𝟙 X) (p ≫ y) (by rw [Category.id_comp, Category.assoc, hy, Category.comp_id])

theorem productRightFiberInclusion_fst (p : X ⟶ S) (q : Y ⟶ S) (y : S ⟶ Y) (hy : y ≫ q = 𝟙 _) :
    productRightFiberInclusion p q y hy ≫ pullback.fst p q = 𝟙 X := pullback.lift_fst _ _ _

theorem productRightFiberInclusion_snd (p : X ⟶ S) (q : Y ⟶ S) (y : S ⟶ Y) (hy : y ≫ q = 𝟙 _) :
    productRightFiberInclusion p q y hy ≫ pullback.snd p q = p ≫ y := pullback.lift_snd _ _ _

theorem productRightFiberInclusion_isPullback (p : X ⟶ S) (q : Y ⟶ S)
    (y : S ⟶ Y) (hy : y ≫ q = 𝟙 _) :
    IsPullback (productRightFiberInclusion p q y hy) p (pullback.snd p q) y := by
  have H : IsPullback (productRightFiberInclusion p q y hy ≫ pullback.fst p q) p p (y ≫ q) := by
    rw [productRightFiberInclusion_fst, hy]
    exact IsPullback.of_id_fst
  exact H.of_right (productRightFiberInclusion_snd p q y hy) (IsPullback.of_hasPullback p q)

def productLeftSection (p : X ⟶ S) (q : Y ⟶ S) (x : S ⟶ X) (hx : x ≫ p = 𝟙 _) :
    Y ⟶ pullback p q :=
  pullback.lift (q ≫ x) (𝟙 Y) (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp])

theorem productLeftSection_snd (p : X ⟶ S) (q : Y ⟶ S) (x : S ⟶ X) (hx : x ≫ p = 𝟙 _) :
    productLeftSection p q x hx ≫ pullback.snd p q = 𝟙 Y := pullback.lift_snd _ _ _

theorem productLeftSection_fst (p : X ⟶ S) (q : Y ⟶ S) (x : S ⟶ X) (hx : x ≫ p = 𝟙 _) :
    productLeftSection p q x hx ≫ pullback.fst p q = q ≫ x := pullback.lift_fst _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.SectionFibers
