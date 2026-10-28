import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ActionLaws
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Multiplicative Line Data -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData

noncomputable section

/-!
# Multiplicative line bundles and multiplicative trivializations on a represented kernel

All fibers are actual pullback sheaves on arbitrary test schemes. The axioms below are the
unit, associativity, and base-change laws for a line-bundle multiplication and its kernel splitting.
They do not assert a descent object or a polarization.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {S : Scheme.{u}} {A : Over S} [GrpObj A] (L : Line.Bundles.LineBundle A.left)

/-- A unital associative line-bundle multiplication, expressed on all actual test-scheme fibers. -/
structure MultiplicativeData where
  product {T : Over S} (a b c : T ⟶ A) (hab : a * b = c) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L a) (Line.Fibers.fiber L b) (Line.Fibers.fiber L c)
  product_isIso {T : Over S} (a b c : T ⟶ A) (hab : a * b = c) :
    IsIso (Bilinear.BilinearPullback.toHom (product a b c hab))
  unitFrame {T : Over S} : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L (1 : T ⟶ A)
  unit_left {T : Over S} (a : T ⟶ A) (ha : 1 * a = a)
      (U : T.left.Opens) (n : Γ(Line.Fibers.fiber L a, U)) :
    (product 1 a a ha).app U (unitFrame.hom.app U (1 : Γ(T.left, U))) n = n
  unit_right {T : Over S} (a : T ⟶ A) (ha : a * 1 = a)
      (U : T.left.Opens) (n : Γ(Line.Fibers.fiber L a, U)) :
    (product a 1 a ha).app U n (unitFrame.hom.app U (1 : Γ(T.left, U))) = n
  associative {T : Over S} (a b c ab bc d : T ⟶ A)
      (hab : a * b = ab) (hbc : b * c = bc) (had : a * bc = d) (hcd : ab * c = d)
      (U : T.left.Opens) (r : Γ(Line.Fibers.fiber L a, U)) (s : Γ(Line.Fibers.fiber L b, U)) (t : Γ(Line.Fibers.fiber L c, U)) :
    (product a bc d had).app U r ((product b c bc hbc).app U s t) =
      (product ab c d hcd).app U ((product a b ab hab).app U r s) t
  product_natural {T T' : Over S} (g : T' ⟶ T) (a b c : T ⟶ A) (hab : a * b = c)
      (a' b' c' : T' ⟶ A) (hab' : a' * b' = c')
      (ha : g ≫ a = a') (hb : g ≫ b = b') (hc : g ≫ c = c') :
    Line.Fibers.pullBilinear L g a b c a' b' c' ha hb hc (product a b c hab) = product a' b' c' hab'
  unit_natural {T T' : Over S} (g : T' ⟶ T) (h : g ≫ (1 : T ⟶ A) = 1) :
    Line.Fibers.pullSection L g 1 1 h unitFrame.hom = (unitFrame (T := T')).hom

variable {B : Over S} [GrpObj B] (f : A ⟶ B) [IsMonHom f] (D : MultiplicativeData L)

attribute [local instance] Kernel.Scheme.kernelGroup

/-- A group-compatible trivialization of the multiplicative line on the actual scheme kernel.
The explicit target point is fixed by its equality with the included kernel point. -/
structure KernelSplitting where
  frame {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ A) (ha : k ≫ Kernel.Scheme.kernelInclusion f = a) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a
  unit {T : Over S} (h : (1 : T ⟶ Kernel.Scheme.kernelObject f) ≫ Kernel.Scheme.kernelInclusion f = 1) :
    frame 1 1 h = D.unitFrame
  multiplicative {T : Over S} (k l m : T ⟶ Kernel.Scheme.kernelObject f) (hm : k * l = m)
      (a b c : T ⟶ A) (ha : k ≫ Kernel.Scheme.kernelInclusion f = a) (hb : l ≫ Kernel.Scheme.kernelInclusion f = b)
      (hc : m ≫ Kernel.Scheme.kernelInclusion f = c) (hab : a * b = c) (U : T.left.Opens) :
    (D.product a b c hab).app U ((frame k a ha).hom.app U (1 : Γ(T.left, U)))
      ((frame l b hb).hom.app U (1 : Γ(T.left, U))) = (frame m c hc).hom.app U (1 : Γ(T.left, U))
  natural {T T' : Over S} (g : T' ⟶ T) (k : T ⟶ Kernel.Scheme.kernelObject f) (k' : T' ⟶ Kernel.Scheme.kernelObject f)
      (hk : g ≫ k = k') (a : T ⟶ A) (a' : T' ⟶ A)
      (ha : k ≫ Kernel.Scheme.kernelInclusion f = a) (ha' : k' ≫ Kernel.Scheme.kernelInclusion f = a') (hg : g ≫ a = a') :
    Line.Fibers.pullSection L g a a' hg (frame k a ha).hom = (frame k' a' ha').hom

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData
