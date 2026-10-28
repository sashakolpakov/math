import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseKernelTransport

/-! # Fiberwise Quotient Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseQuotientTransport

noncomputable section

/-!
# Coordinate quotient transport from represented kernel differences
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseKernelCoordinates OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {E A B X : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  (p : E ⟶ A) (r : E ⟶ X) (f : A ⟶ B) [IsMonHom f]
  (replace : A ⊗ E ⟶ E) (hp : replace ≫ p = fst A E) (hr : replace ≫ r = snd A E ≫ r)
  (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication p r L) (K : FiberwiseMultiplication.KernelFrames p r L f D)

attribute [local instance] Kernel.Scheme.kernelGroup Kernel.Scheme.kernelGroup_commutative

/-- Equality in one coordinate quotient with the other coordinate held fixed. -/
def Relation {T : Over S} (x y : T ⟶ E) : Prop :=
  (x ≫ p) ≫ f = (y ≫ p) ≫ f ∧ x ≫ r = y ≫ r

/-- Use the actual represented kernel difference to construct the coordinate quotient transport. -/
def transport {T : Over S} (x y : T ⟶ E) (h : Relation p r f x y) : Line.Fibers.fiber L x ⟶ Line.Fibers.fiber L y :=
  FiberwiseKernelTransport.transport p r f replace hp hr L D K x y
    (Kernel.Pair.pointDifference f (x ≫ p) (y ≫ p) h.1)
    (Kernel.Linearization.difference_translates f (x ≫ p) (y ≫ p) h.1) h.2

/-- An equal presentation of the represented difference gives the same actual transport. -/
theorem transport_using {T : Over S} (x y : T ⟶ E) (h : Relation p r f x y)
    (k : T ⟶ Kernel.Scheme.kernelObject f) (hk : Kernel.Pair.pointDifference f (x ≫ p) (y ≫ p) h.1 = k)
    (hxy : (x ≫ p) * (k ≫ Kernel.Scheme.kernelInclusion f) = y ≫ p) :
    transport p r f replace hp hr L D K x y h =
      FiberwiseKernelTransport.transport p r f replace hp hr L D K x y k hxy h.2 := by
  cases hk
  rfl

/-- Quotient transport along a point itself is the actual identity. -/
theorem transport_self {T : Over S} (x : T ⟶ E) (h : Relation p r f x x) :
    transport p r f replace hp hr L D K x x h = 𝟙 _ := by
  have hu : (x ≫ p) * ((1 : T ⟶ Kernel.Scheme.kernelObject f) ≫ Kernel.Scheme.kernelInclusion f) = x ≫ p := by
    rw [MonObj.one_comp, mul_one]
  exact (transport_using p r f replace hp hr L D K x x h 1
    (Kernel.Pair.pointDifference_self f (x ≫ p)) hu).trans
      (FiberwiseKernelTransport.transport_unit p r f replace hp hr L D K x hu h.2)

/-- The represented kernel-difference cocycle proves the coordinate quotient cocycle. -/
theorem transport_comp {T : Over S} (x y z : T ⟶ E)
    (hxy : Relation p r f x y) (hyz : Relation p r f y z) (hxz : Relation p r f x z) :
    transport p r f replace hp hr L D K x y hxy ≫ transport p r f replace hp hr L D K y z hyz =
      transport p r f replace hp hr L D K x z hxz :=
  FiberwiseKernelTransport.transport_mul p r f replace hp hr L D K x y z
    (Kernel.Pair.pointDifference f (x ≫ p) (y ≫ p) hxy.1) (Kernel.Pair.pointDifference f (y ≫ p) (z ≫ p) hyz.1)
    (Kernel.Pair.pointDifference f (x ≫ p) (z ≫ p) hxz.1)
    (Kernel.Linearization.difference_translates f _ _ hxy.1)
    (Kernel.Linearization.difference_translates f _ _ hyz.1)
    (Kernel.Linearization.difference_translates f _ _ hxz.1) hxy.2 hyz.2 hxz.2
    (Kernel.Pair.pointDifference_cocycle f (x ≫ p) (y ≫ p) (z ≫ p) hxy.1 hyz.1).symm

/-- The constructed quotient transport commutes with every change of test scheme. -/
theorem transport_pullback {T T' : Over S} (g : T' ⟶ T) (x y : T ⟶ E)
    (h : Relation p r f x y) (x' y' : T' ⟶ E) (h' : Relation p r f x' y')
    (hgx : g ≫ x = x') (hgy : g ≫ y = y') :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Geometric.KernelLinearization.overModulePullbacks S)
      (transport p r f replace hp hr L D K x y h) g x' y' hgx hgy =
        transport p r f replace hp hr L D K x' y' h' := by
  have hx : g ≫ (x ≫ p) = x' ≫ p := (Category.assoc g x p).symm.trans
    (congrArg (fun a => a ≫ p) hgx)
  have hy : g ≫ (y ≫ p) = y' ≫ p := (Category.assoc g y p).symm.trans
    (congrArg (fun a => a ≫ p) hgy)
  exact FiberwiseKernelTransport.transport_pullback p r f replace hp hr L D K g x y
    (Kernel.Pair.pointDifference f (x ≫ p) (y ≫ p) h.1)
    (Kernel.Linearization.difference_translates f _ _ h.1) h.2 x' y'
    (Kernel.Pair.pointDifference f (x' ≫ p) (y' ≫ p) h'.1)
    (Kernel.Linearization.difference_translates f _ _ h'.1) h'.2 hgx hgy
    (Kernel.Linearization.difference_naturality f g _ _ h.1 _ _ h'.1 hx hy)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseQuotientTransport
