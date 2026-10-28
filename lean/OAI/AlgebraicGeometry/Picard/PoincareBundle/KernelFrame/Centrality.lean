import OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.FrameCentrality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.TransverseFrames

/-! # Centrality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Centrality

noncomputable section

/-!
# Centrality of actual kernel frames and its geometric transport
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FiberIsomorphisms OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationIso OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.FrameCentrality

variable {S : Scheme.{u}} {E A B X K : Over S} [GrpObj A] [GrpObj B]
  {p : E ⟶ A} {r : E ⟶ X} (f : A ⟶ B) [IsMonHom f]
  {L : Line.Bundles.LineBundle E.left} {D : FiberwiseMultiplication.Multiplication p r L}

/-- A canonical kernel frame can be moved between the two inputs of the genuine bilinear product. -/
def Central (F : FiberwiseMultiplication.KernelFrames p r L f D) : Prop :=
  ∀ (T : Over S) (k : T ⟶ Kernel.Scheme.kernelObject f) (a x y : T ⟶ E)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ p)
    (hax : FiberwiseMultiplication.ProductRel p r a x y) (hxa : FiberwiseMultiplication.ProductRel p r x a y)
    (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L x, U)),
    (D.product a x y hax).app U ((F.frame k a ha).hom.app U (1 : Γ(T.left, U))) m =
      (D.product x a y hxa).app U m ((F.frame k a ha).hom.app U (1 : Γ(T.left, U)))

/-- Changing equal coordinates preserves centrality of the actual frames. -/
theorem congrCoordinates (F : FiberwiseMultiplication.KernelFrames p r L f D) {p' : E ⟶ A} {r' : E ⟶ X}
    (hp : p = p') (hr : r = r') (hc : Central f F) :
    Central f (Kernel.FramesPullback.congrCoordinates f L D F hp hr) := by
  cases hp
  cases hr
  exact hc

/-- The canonical geometric pullback of a central frame system remains central. -/
theorem pullback (q : K ⟶ E) (F : FiberwiseMultiplication.KernelFrames p r L f D) (hc : Central f F) :
    Central f (Kernel.FramesPullback.pullbackFrames p r q f L D F) := by
  intro T k a x y ha hax hxa U m
  exact Neutral.FrameCentrality.central_transport (D.product _ _ _ (FiberwiseMultiplicationPullback.imageRel p r q a x y hax))
    (D.product _ _ _ (FiberwiseMultiplicationPullback.imageRel p r q x a y hxa))
    (Pulled.LineBilinear.fiberComparison q L a (a ≫ q) rfl).symm (Pulled.LineBilinear.fiberComparison q L x (x ≫ q) rfl).symm
    (Pulled.LineBilinear.fiberComparison q L y (y ≫ q) rfl).symm
    (F.frame k (a ≫ q) (Kernel.FramesPullback.imageKernel p q f k a ha)).hom
    (hc T k _ _ _ (Kernel.FramesPullback.imageKernel p q f k a ha)
      (FiberwiseMultiplicationPullback.imageRel p r q a x y hax) (FiberwiseMultiplicationPullback.imageRel p r q x a y hxa)) U m

/-- An actual line-bundle isomorphism transports the full centrality law. -/
theorem iso (M : Line.Bundles.LineBundle E.left) (e : L.sheaf ≅ M.sheaf)
    (F : FiberwiseMultiplication.KernelFrames p r L f D) (hc : Central f F) :
    Central f (FiberwiseMultiplicationIso.transportKernelFrames p r L M e D f F) := by
  intro T k a x y ha hax hxa U m
  exact Neutral.FrameCentrality.central_transport (D.product a x y hax) (D.product x a y hxa)
    (Line.FiberIsomorphisms.fiberIso L M e a) (Line.FiberIsomorphisms.fiberIso L M e x) (Line.FiberIsomorphisms.fiberIso L M e y) (F.frame k a ha).hom
    (hc T k a x y ha hax hxa) U m

end

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (L : Line.Bundles.LineBundle (A ⊗ A).left) (D : FiberwiseMultiplication.Multiplication (fst A A) (snd A A) L)
  (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj L.sheaf ≅ L.sheaf)
  (f : A ⟶ B) [IsMonHom f] (F : FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) L f D)

/-- Symmetry constructs centrality of the actual second kernel-frame system. -/
theorem second_central (hc : Central f F) : Central f (Symmetric.MultiplicativeFrames.secondFrames L D e f F) := by
  apply iso
  apply congrCoordinates
  exact Centrality.pullback f (β_ A A).hom F hc

/-- Identifying the actual transported product preserves centrality of the same kernel frames. -/
theorem compatible_second_central (Dv : FiberwiseMultiplication.Multiplication (snd A A) (fst A A) L)
    (hv : Symmetric.MultiplicativeFrames.secondMultiplication L D e = Dv) (hc : Central f F) :
    Central f (Symmetric.TransverseFrames.secondFramesOfCompatible L D Dv e f F hv) := by
  cases hv
  exact second_central L D e f F hc

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Centrality
