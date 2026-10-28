import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.TransportGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OverSquare

/-! # Square Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareTransport

noncomputable section

/-!
# Native product-square descent has exactly the genuine product transports
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.TransportGluing

section KernelPair

variable {S : Scheme.{u}} {K Q : Over S} (f : K ⟶ Q)

/-- The common quotient map of the actual underlying scheme kernel pair. -/
def testBase : pullback f.left f.left ⟶ Q.left := pullback.snd f.left f.left ≫ f.left

/-- The first actual kernel-pair point with the common quotient-induced base structure. -/
def firstPoint : UnderlyingDescent.testObject (testBase f) ⟶ K :=
  UnderlyingDescent.coverMap (fun (_ : PUnit.{1}) => f) (i := PUnit.unit)
    (testBase f) (pullback.fst f.left f.left) pullback.condition

/-- The second actual kernel-pair point on the same object over the base. -/
def secondPoint : UnderlyingDescent.testObject (testBase f) ⟶ K :=
  UnderlyingDescent.coverMap (fun (_ : PUnit.{1}) => f) (i := PUnit.unit)
    (testBase f) (pullback.snd f.left f.left) rfl

/-- These two genuine test points have equal quotient images. -/
theorem point_images : firstPoint f ≫ f = secondPoint f ≫ f :=
  Over.OverMorphism.ext pullback.condition

end KernelPair

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hc : RectangularTransport.Commutes f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv))

/-- The native original product descent datum from the already constructed commuting transports. -/
def originalDatum : (Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => f ⊗ₘ g) :=
  RectangularTransport.toDescentData f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv) hc

variable (i : (A ⊗ A) ⊗ X ⟶ A ⊗ X) (j : (B ⊗ B) ⊗ Y ⟶ B ⊗ Y)
  (hij : ((f ⊗ₘ f) ⊗ₘ g) ≫ j = i ≫ (f ⊗ₘ g))

/-- Pulling the original datum through an input or output square produces its actual transported sheaf maps. -/
theorem pulledHom_transport {T : Over S} (base : T ⟶ (B ⊗ B) ⊗ Y) (p q : T ⟶ (A ⊗ A) ⊗ X)
    (hp : p ≫ ((f ⊗ₘ f) ⊗ₘ g) = base) (hq : q ≫ ((f ⊗ₘ f) ⊗ₘ g) = base) :
    (Recovered.OverSquare.pulledDatum (f ⊗ₘ g) ((f ⊗ₘ f) ⊗ₘ g) i j hij.symm
      (originalDatum f g L Dh Dv Kh Kv hc)).hom base (i₁ := PUnit.unit) (i₂ := PUnit.unit) p q hp hq =
    TransportGluing.productTransport f g L Dh Dv Kh Kv p q i
      (TransportGluing.square_images _ _ _ _ hij p q (hp.trans hq.symm)) := by
  rw [Recovered.OverSquare.pulledHom]
  unfold TransportGluing.productTransport
  exact (FiberBilinearGluing.fiberTransport_eq_comp L p q i
    (RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv)
      (p ≫ i) (q ≫ i) (TransportGluing.square_images _ _ _ _ hij p q (hp.trans hq.symm)))).symm

/-- The underlying kernel-pair gluing equals that same genuine transport on the common test object. -/
theorem relationGluing_transport :
    (Geometric.CechInvariant.relationGluing ((f ⊗ₘ f) ⊗ₘ g).left
      (Recovered.OverSquare.underlyingDatum (f ⊗ₘ g) ((f ⊗ₘ f) ⊗ₘ g) i j hij.symm
        (originalDatum f g L Dh Dv Kh Kv hc))).hom =
      TransportGluing.productTransport f g L Dh Dv Kh Kv (firstPoint ((f ⊗ₘ f) ⊗ₘ g)) (secondPoint ((f ⊗ₘ f) ⊗ₘ g)) i
        (TransportGluing.square_images _ _ _ _ hij _ _ (point_images ((f ⊗ₘ f) ⊗ₘ g))) :=
  pulledHom_transport f g L Dh Dv Kh Kv hc i j hij
    (UnderlyingDescent.baseMap (testBase ((f ⊗ₘ f) ⊗ₘ g))) _ _
    (UnderlyingDescent.coverMap_base (fun (_ : PUnit.{1}) => ((f ⊗ₘ f) ⊗ₘ g)) (i := PUnit.unit)
      (testBase ((f ⊗ₘ f) ⊗ₘ g)) (pullback.fst _ _) pullback.condition)
    (UnderlyingDescent.coverMap_base (fun (_ : PUnit.{1}) => ((f ⊗ₘ f) ⊗ₘ g)) (i := PUnit.unit)
      (testBase ((f ⊗ₘ f) ⊗ₘ g)) (pullback.snd _ _) rfl)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareTransport
