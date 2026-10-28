import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData

/-! # Fiberwise Multiplication -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

noncomputable section

/-!
# Multiplicative line fibers along one coordinate of a biextension

The line sheaf remains on the original scheme. The projection `p` is the group coordinate and `r`
is the fixed coordinate. All products and kernel frames are actual sheaf maps on every test scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {S : Scheme.{u}} {E A X : Over S} [GrpObj A]
  (p : E ⟶ A) (r : E ⟶ X) (L : Line.Bundles.LineBundle E.left)

/-- Three test points describe multiplication in the group coordinate at one fixed second coordinate. -/
def ProductRel {T : Over S} (a b c : T ⟶ E) : Prop :=
  (a ≫ p) * (b ≫ p) = c ≫ p ∧ a ≫ r = b ≫ r ∧ a ≫ r = c ≫ r

/-- The ordinary unit, associativity, and pullback laws of a fiberwise line multiplication. -/
structure Multiplication where
  product {T : Over S} (a b c : T ⟶ E) (h : ProductRel p r a b c) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L a) (Line.Fibers.fiber L b) (Line.Fibers.fiber L c)
  product_isIso {T : Over S} (a b c : T ⟶ E) (h : ProductRel p r a b c) :
    IsIso (Bilinear.BilinearPullback.toHom (product a b c h))
  unitFrame {T : Over S} (a : T ⟶ E) (ha : a ≫ p = 1) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a
  unit_left {T : Over S} (a x : T ⟶ E) (ha : a ≫ p = 1) (h : ProductRel p r a x x)
      (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L x, U)) :
    (product a x x h).app U ((unitFrame a ha).hom.app U (1 : Γ(T.left, U))) m = m
  unit_right {T : Over S} (x a : T ⟶ E) (ha : a ≫ p = 1) (h : ProductRel p r x a x)
      (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L x, U)) :
    (product x a x h).app U m ((unitFrame a ha).hom.app U (1 : Γ(T.left, U))) = m
  associative {T : Over S} (a b c ab bc d : T ⟶ E)
      (hab : ProductRel p r a b ab) (hbc : ProductRel p r b c bc)
      (had : ProductRel p r a bc d) (hcd : ProductRel p r ab c d)
      (U : T.left.Opens) (s : Γ(Line.Fibers.fiber L a, U)) (t : Γ(Line.Fibers.fiber L b, U)) (m : Γ(Line.Fibers.fiber L c, U)) :
    (product a bc d had).app U s ((product b c bc hbc).app U t m) =
      (product ab c d hcd).app U ((product a b ab hab).app U s t) m
  product_natural {T T' : Over S} (g : T' ⟶ T) (a b c : T ⟶ E) (h : ProductRel p r a b c)
      (a' b' c' : T' ⟶ E) (h' : ProductRel p r a' b' c')
      (ha : g ≫ a = a') (hb : g ≫ b = b') (hc : g ≫ c = c') :
    Line.Fibers.pullBilinear L g a b c a' b' c' ha hb hc (product a b c h) = product a' b' c' h'
  unit_natural {T T' : Over S} (g : T' ⟶ T) (a : T ⟶ E) (a' : T' ⟶ E)
      (ha : a ≫ p = 1) (ha' : a' ≫ p = 1) (hga : g ≫ a = a') :
    Line.Fibers.pullSection L g a a' hga (unitFrame a ha).hom = (unitFrame a' ha').hom

variable {B : Over S} [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  (D : Multiplication p r L)

attribute [local instance] Kernel.Scheme.kernelGroup

/-- A multiplicative kernel frame along this coordinate, with its genuine geometric pullback law. -/
structure KernelFrames where
  frame {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ E) (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ p) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a
  unit {T : Over S} (a : T ⟶ E) (ha : a ≫ p = 1)
      (hk : (1 : T ⟶ Kernel.Scheme.kernelObject f) ≫ Kernel.Scheme.kernelInclusion f = a ≫ p) :
    frame 1 a hk = D.unitFrame a ha
  multiplicative {T : Over S} (k l m : T ⟶ Kernel.Scheme.kernelObject f) (hm : k * l = m)
      (a b c : T ⟶ E) (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ p)
      (hb : l ≫ Kernel.Scheme.kernelInclusion f = b ≫ p) (hc : m ≫ Kernel.Scheme.kernelInclusion f = c ≫ p)
      (hab : ProductRel p r a b c) (U : T.left.Opens) :
    (D.product a b c hab).app U ((frame k a ha).hom.app U (1 : Γ(T.left, U)))
      ((frame l b hb).hom.app U (1 : Γ(T.left, U))) = (frame m c hc).hom.app U (1 : Γ(T.left, U))
  natural {T T' : Over S} (g : T' ⟶ T) (k : T ⟶ Kernel.Scheme.kernelObject f) (k' : T' ⟶ Kernel.Scheme.kernelObject f)
      (hgk : g ≫ k = k') (a : T ⟶ E) (a' : T' ⟶ E)
      (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ p) (ha' : k' ≫ Kernel.Scheme.kernelInclusion f = a' ≫ p)
      (hga : g ≫ a = a') :
    Line.Fibers.pullSection L g a a' hga (frame k a ha).hom = (frame k' a' ha').hom

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication
