import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationPullbackSquare
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterProducts

/-! # Multiplication Square Products -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationSquareProducts

noncomputable section

/-! The full coordinate-square multiplication retains its exact transported bilinear product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationPullbackSquare

variable {S : Scheme.{u}} {E F A B X Y : Over S} [GrpObj A] [GrpObj B]
  (p : E ⟶ A) (r : E ⟶ X) (p' : F ⟶ B) (r' : F ⟶ Y)
  (q : E ⟶ F) (f : A ⟶ B) [IsMonHom f] (g : X ⟶ Y)
  (hp : q ≫ p' = p ≫ f) (hr : q ≫ r' = r ≫ g)

include hp hr in
/-- A product relation maps to the original relation through the two actual coordinate maps. -/
theorem mapped_relation {T : Over S} (a b c : T ⟶ E) (h : FiberwiseMultiplication.ProductRel p r a b c) :
    FiberwiseMultiplication.ProductRel p' r' (a ≫ q) (b ≫ q) (c ≫ q) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Category.assoc, hp, MonObj.mul_comp] using congrArg (fun z => z ≫ f) h.1
  · simpa only [Category.assoc, hr] using congrArg (fun z => z ≫ g) h.2.1
  · simpa only [Category.assoc, hr] using congrArg (fun z => z ≫ g) h.2.2

variable (L : Line.Bundles.LineBundle F.left) (D : FiberwiseMultiplication.Multiplication p' r' L)

/-- Both coordinate restrictions leave the underlying transported sheaf product unchanged. -/
theorem product_eq {T : Over S} (a b c : T ⟶ E) (h : FiberwiseMultiplication.ProductRel p r a b c) :
    (MultiplicationPullbackSquare.multiplication p r p' r' q f g hp hr L D).product a b c h =
    Pulled.LineBilinear.transport q L a b c (a ≫ q) (b ≫ q) (c ≫ q) rfl rfl rfl
      (D.product _ _ _ (mapped_relation p r p' r' q f g hp hr a b c h)) := by
  have hq : FiberwiseMultiplication.ProductRel (q ≫ p') (q ≫ r') a b c := by
    simpa only [FiberwiseMultiplication.ProductRel, Category.assoc] using mapped_relation p r p' r' q f g hp hr a b c h
  unfold MultiplicationPullbackSquare.multiplication MultiplicationFixedMap.restrictFixed
    MultiplicationCoordinateMap.restrictCoordinate
  dsimp only
  unfold MultiplicationPullbackSquare.imageMultiplication
  rw [Vertical.ParameterProducts.congrCoordinates_product (L.pullback q.left)
    (FiberwiseMultiplicationPullback.pullbackMultiplication p' r' q L D) hp hr a b c hq]
  rfl

/-- Specifying the three target points only replaces the corresponding equality comparisons. -/
theorem product_eq_to {T : Over S} (a b c : T ⟶ E) (h : FiberwiseMultiplication.ProductRel p r a b c)
    (a' b' c' : T ⟶ F) (ha : a ≫ q = a') (hb : b ≫ q = b') (hc : c ≫ q = c')
    (h' : FiberwiseMultiplication.ProductRel p' r' a' b' c') :
    (MultiplicationPullbackSquare.multiplication p r p' r' q f g hp hr L D).product a b c h =
      Pulled.LineBilinear.transport q L a b c a' b' c' ha hb hc (D.product a' b' c' h') := by
  subst a'
  subst b'
  subst c'
  exact product_eq p r p' r' q f g hp hr L D a b c h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationSquareProducts
