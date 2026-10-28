import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineSection
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.AlgebraTransport

/-! # Fiberwise Multiplication Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback

noncomputable section

/-!
# Construct the actual fiberwise multiplication on a pulled-back line bundle
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineSection

variable {S : Scheme.{u}} {K E A X : Over S} [GrpObj A] (p : E ⟶ A) (r : E ⟶ X) (q : K ⟶ E)

/-- The pulled-back coordinate multiplication relation maps to the original coordinate relation. -/
theorem imageRel {T : Over S} (a b c : T ⟶ K) (h : FiberwiseMultiplication.ProductRel (q ≫ p) (q ≫ r) a b c) :
    FiberwiseMultiplication.ProductRel p r (a ≫ q) (b ≫ q) (c ≫ q) :=
  ⟨by simpa only [Category.assoc] using h.1,
    by simpa only [Category.assoc] using h.2.1, by simpa only [Category.assoc] using h.2.2⟩

/-- A pulled-back unit point maps to an actual unit point in the original group coordinate. -/
theorem imageUnit {T : Over S} (a : T ⟶ K) (h : a ≫ (q ≫ p) = 1) : (a ≫ q) ≫ p = 1 := by
  simpa only [Category.assoc] using h

/-- Images of test points commute with change of test scheme. -/
theorem image_natural {T T' : Over S} (g : T' ⟶ T) (a : T ⟶ K) (a' : T' ⟶ K) (ha : g ≫ a = a') :
    g ≫ (a ≫ q) = a' ≫ q := (Category.assoc g a q).symm.trans (congrArg (fun b => b ≫ q) ha)

variable (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication p r L)

/-- The pulled-back product is the actual original product transported through the canonical fiber comparisons. -/
def product {T : Over S} (a b c : T ⟶ K) (h : FiberwiseMultiplication.ProductRel (q ≫ p) (q ≫ r) a b c) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber (L.pullback q.left) a) (Line.Fibers.fiber (L.pullback q.left) b) (Line.Fibers.fiber (L.pullback q.left) c) :=
  Pulled.LineBilinear.transport q L a b c (a ≫ q) (b ≫ q) (c ≫ q) rfl rfl rfl
    (D.product (a ≫ q) (b ≫ q) (c ≫ q) (imageRel p r q a b c h))

/-- The actual pulled-back product is still a bilinear isomorphism. -/
theorem product_isIso {T : Over S} (a b c : T ⟶ K) (h : FiberwiseMultiplication.ProductRel (q ≫ p) (q ≫ r) a b c) :
    IsIso (Bilinear.BilinearPullback.toHom (FiberwiseMultiplicationPullback.product p r q L D a b c h)) := by
  have hi : IsIso (Bilinear.BilinearPullback.toHom (D.product (a ≫ q) (b ≫ q) (c ≫ q) (imageRel p r q a b c h))) :=
    D.product_isIso _ _ _ _
  unfold FiberwiseMultiplicationPullback.product Pulled.LineBilinear.transport
  rw [Bilinear.Transport.toHom_transport]
  infer_instance

/-- The original actual unit frame supplies the normalized unit frame on the pulled-back line. -/
def unitFrame {T : Over S} (a : T ⟶ K) (ha : a ≫ (q ≫ p) = 1) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber (L.pullback q.left) a :=
  Pulled.LineSection.transportFrame q L a (a ≫ q) rfl (D.unitFrame (a ≫ q) (imageUnit p q a ha))

/-- The actual left-unit law is inherited through the canonical comparisons. -/
theorem unit_left {T : Over S} (a x : T ⟶ K) (ha : a ≫ (q ≫ p) = 1)
    (h : FiberwiseMultiplication.ProductRel (q ≫ p) (q ≫ r) a x x) (U : T.left.Opens) (m : Γ(Line.Fibers.fiber (L.pullback q.left) x, U)) :
    (FiberwiseMultiplicationPullback.product p r q L D a x x h).app U ((FiberwiseMultiplicationPullback.unitFrame p r q L D a ha).hom.app U (1 : Γ(T.left, U))) m = m :=
  Bilinear.AlgebraTransport.unit_left (D.product _ _ _ (imageRel p r q a x x h))
    (Pulled.LineBilinear.fiberComparison q L a (a ≫ q) rfl).symm (Pulled.LineBilinear.fiberComparison q L x (x ≫ q) rfl).symm
    (D.unitFrame _ (imageUnit p q a ha)).hom (D.unit_left _ _ (imageUnit p q a ha) _) U m

/-- The actual right-unit law is inherited through the canonical comparisons. -/
theorem unit_right {T : Over S} (x a : T ⟶ K) (ha : a ≫ (q ≫ p) = 1)
    (h : FiberwiseMultiplication.ProductRel (q ≫ p) (q ≫ r) x a x) (U : T.left.Opens) (m : Γ(Line.Fibers.fiber (L.pullback q.left) x, U)) :
    (FiberwiseMultiplicationPullback.product p r q L D x a x h).app U m ((FiberwiseMultiplicationPullback.unitFrame p r q L D a ha).hom.app U (1 : Γ(T.left, U))) = m :=
  Bilinear.AlgebraTransport.unit_right (D.product _ _ _ (imageRel p r q x a x h))
    (Pulled.LineBilinear.fiberComparison q L x (x ≫ q) rfl).symm (Pulled.LineBilinear.fiberComparison q L a (a ≫ q) rfl).symm
    (D.unitFrame _ (imageUnit p q a ha)).hom (D.unit_right _ _ (imageUnit p q a ha) _) U m

/-- Associativity of the original actual line products proves associativity of the pulled-back products. -/
theorem associative {T : Over S} (a b c ab bc d : T ⟶ K)
    (hab : FiberwiseMultiplication.ProductRel (q ≫ p) (q ≫ r) a b ab) (hbc : FiberwiseMultiplication.ProductRel (q ≫ p) (q ≫ r) b c bc)
    (had : FiberwiseMultiplication.ProductRel (q ≫ p) (q ≫ r) a bc d) (hcd : FiberwiseMultiplication.ProductRel (q ≫ p) (q ≫ r) ab c d)
    (U : T.left.Opens) (s : Γ(Line.Fibers.fiber (L.pullback q.left) a, U)) (t : Γ(Line.Fibers.fiber (L.pullback q.left) b, U))
    (m : Γ(Line.Fibers.fiber (L.pullback q.left) c, U)) :
    (FiberwiseMultiplicationPullback.product p r q L D a bc d had).app U s ((FiberwiseMultiplicationPullback.product p r q L D b c bc hbc).app U t m) =
      (FiberwiseMultiplicationPullback.product p r q L D ab c d hcd).app U ((FiberwiseMultiplicationPullback.product p r q L D a b ab hab).app U s t) m :=
  Bilinear.AlgebraTransport.associative
    (D.product _ _ _ (imageRel p r q b c bc hbc)) (D.product _ _ _ (imageRel p r q a bc d had))
    (D.product _ _ _ (imageRel p r q a b ab hab)) (D.product _ _ _ (imageRel p r q ab c d hcd))
    (Pulled.LineBilinear.fiberComparison q L a (a ≫ q) rfl).symm (Pulled.LineBilinear.fiberComparison q L b (b ≫ q) rfl).symm
    (Pulled.LineBilinear.fiberComparison q L c (c ≫ q) rfl).symm (Pulled.LineBilinear.fiberComparison q L ab (ab ≫ q) rfl).symm
    (Pulled.LineBilinear.fiberComparison q L bc (bc ≫ q) rfl).symm (Pulled.LineBilinear.fiberComparison q L d (d ≫ q) rfl).symm
    (D.associative _ _ _ _ _ _ _ _ _ _) U s t m

/-- The pulled-back multiplication has the full native geometric naturality on all test schemes. -/
theorem product_natural {T T' : Over S} (g : T' ⟶ T) (a b c : T ⟶ K)
    (h : FiberwiseMultiplication.ProductRel (q ≫ p) (q ≫ r) a b c) (a' b' c' : T' ⟶ K)
    (h' : FiberwiseMultiplication.ProductRel (q ≫ p) (q ≫ r) a' b' c')
    (ha : g ≫ a = a') (hb : g ≫ b = b') (hc : g ≫ c = c') :
    Line.Fibers.pullBilinear (L.pullback q.left) g a b c a' b' c' ha hb hc (FiberwiseMultiplicationPullback.product p r q L D a b c h) =
      FiberwiseMultiplicationPullback.product p r q L D a' b' c' h' := by
  have he := Pulled.LineBilinear.transport_pullback q L g a b c (a ≫ q) (b ≫ q) (c ≫ q) rfl rfl rfl
    a' b' c' (a' ≫ q) (b' ≫ q) (c' ≫ q) rfl rfl rfl ha hb hc
    (image_natural q g a a' ha) (image_natural q g b b' hb) (image_natural q g c c' hc)
    (D.product _ _ _ (imageRel p r q a b c h))
  rw [D.product_natural g _ _ _ _ _ _ _ (imageRel p r q a' b' c' h')
    (image_natural q g a a' ha) (image_natural q g b b' hb) (image_natural q g c c' hc)] at he
  exact he

/-- The pulled-back normalized unit frames have their genuine geometric naturality. -/
theorem unit_natural {T T' : Over S} (g : T' ⟶ T) (a : T ⟶ K) (a' : T' ⟶ K)
    (ha : a ≫ (q ≫ p) = 1) (ha' : a' ≫ (q ≫ p) = 1) (hga : g ≫ a = a') :
    Line.Fibers.pullSection (L.pullback q.left) g a a' hga (FiberwiseMultiplicationPullback.unitFrame p r q L D a ha).hom =
      (FiberwiseMultiplicationPullback.unitFrame p r q L D a' ha').hom :=
  Pulled.LineSection.transportFrame_natural q L g a (a ≫ q) rfl a' (a' ≫ q) rfl hga (image_natural q g a a' hga)
    _ _ (D.unit_natural g _ _ (imageUnit p q a ha) (imageUnit p q a' ha') (image_natural q g a a' hga))

/-- The full fiberwise multiplication on the actual pulled-back line is constructed from the original multiplication. -/
def pullbackMultiplication : FiberwiseMultiplication.Multiplication (q ≫ p) (q ≫ r) (L.pullback q.left) where
  product := fun {_T} a b c h => FiberwiseMultiplicationPullback.product p r q L D a b c h
  product_isIso := fun {_T} a b c h => FiberwiseMultiplicationPullback.product_isIso p r q L D a b c h
  unitFrame := fun {_T} a ha => FiberwiseMultiplicationPullback.unitFrame p r q L D a ha
  unit_left := fun {_T} a x ha h U m => FiberwiseMultiplicationPullback.unit_left p r q L D a x ha h U m
  unit_right := fun {_T} x a ha h U m => FiberwiseMultiplicationPullback.unit_right p r q L D x a ha h U m
  associative := fun {_T} a b c ab bc d hab hbc had hcd U s t m =>
    FiberwiseMultiplicationPullback.associative p r q L D a b c ab bc d hab hbc had hcd U s t m
  product_natural := fun {_T _T'} g a b c h a' b' c' h' ha hb hc =>
    FiberwiseMultiplicationPullback.product_natural p r q L D g a b c h a' b' c' h' ha hb hc
  unit_natural := fun {_T _T'} g a a' ha ha' hga => FiberwiseMultiplicationPullback.unit_natural p r q L D g a a' ha ha' hga

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback
