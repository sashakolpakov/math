import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinates

/-! # Frame Centrality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.FrameCentrality

noncomputable section

/-!
# Neutral frames are central in the genuine line multiplication, including after pullback
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.AlgebraTransport

/-- A central inserted section stays central after consistent transport of the three line fibers. -/
theorem central_transport {T : Scheme.{u}} {M N P M' N' P' : T.Modules}
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (γ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap N M P)
    (a : M ≅ M') (b : N ≅ N') (c : P ≅ P') (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T ⟶ M)
    (h : ∀ (U : T.Opens) (m : Γ(N, U)),
      β.app U (s.app U (1 : Γ(T, U))) m = γ.app U m (s.app U (1 : Γ(T, U))))
    (U : T.Opens) (m : Γ(N', U)) :
    (Bilinear.Transport.transport β a b c).app U ((s ≫ a.hom).app U (1 : Γ(T, U))) m =
      (Bilinear.Transport.transport γ b a c).app U m ((s ≫ a.hom).app U (1 : Γ(T, U))) := by
  change c.hom.app U (β.app U (a.inv.app U (a.hom.app U (s.app U (1 : Γ(T, U))))) (b.inv.app U m)) =
    c.hom.app U (γ.app U (b.inv.app U m) (a.inv.app U (a.hom.app U (s.app U (1 : Γ(T, U))))))
  rw [Bilinear.AlgebraTransport.inv_hom_app, h]

variable {S : Scheme.{u}} {E A X K : Over S} [GrpObj A]
  {p : E ⟶ A} {r : E ⟶ X} {L : Line.Bundles.LineBundle E.left}

/-- Centrality of the normalized neutral frame is stated on the actual bilinear line fibers. -/
def NeutralCentral (D : FiberwiseMultiplication.Multiplication p r L) : Prop :=
  ∀ (T : Over S) (a x y : T ⟶ E) (ha : a ≫ p = 1)
    (hax : FiberwiseMultiplication.ProductRel p r a x y) (hxa : FiberwiseMultiplication.ProductRel p r x a y)
    (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L x, U)),
    (D.product a x y hax).app U ((D.unitFrame a ha).hom.app U (1 : Γ(T.left, U))) m =
      (D.product x a y hxa).app U m ((D.unitFrame a ha).hom.app U (1 : Γ(T.left, U)))

/-- On actual product-coordinate spaces, multiplication by a neutral frame is central by the two unit laws. -/
theorem neutral_central [Mono (lift p r)] (D : FiberwiseMultiplication.Multiplication p r L) : NeutralCentral D := by
  intro T a x y ha hax hxa U m
  have hxy : x = y := by
    apply (cancel_mono (lift p r)).mp
    rw [comp_lift, comp_lift]
    apply congrArg₂ lift
    · simpa only [ha, one_mul] using hax.1
    · exact hxa.2.2
  subst y
  rw [D.unit_left a x ha hax, D.unit_right x a ha hxa]

/-- Changing equal coordinate maps preserves neutral-frame centrality. -/
theorem congrCoordinates (D : FiberwiseMultiplication.Multiplication p r L) {p' : E ⟶ A} {r' : E ⟶ X}
    (hp : p = p') (hr : r = r') (h : NeutralCentral D) :
    NeutralCentral (MultiplicationCoordinates.congrCoordinates D hp hr) := by
  cases hp
  cases hr
  exact h

/-- Neutral-frame centrality survives arbitrary geometric pullback of the genuine multiplication. -/
theorem pullback (q : K ⟶ E) (D : FiberwiseMultiplication.Multiplication p r L) (h : NeutralCentral D) :
    NeutralCentral (FiberwiseMultiplicationPullback.pullbackMultiplication p r q L D) := by
  intro T a x y ha hax hxa U m
  exact central_transport (D.product _ _ _ (FiberwiseMultiplicationPullback.imageRel p r q a x y hax))
    (D.product _ _ _ (FiberwiseMultiplicationPullback.imageRel p r q x a y hxa))
    (Pulled.LineBilinear.fiberComparison q L a (a ≫ q) rfl).symm (Pulled.LineBilinear.fiberComparison q L x (x ≫ q) rfl).symm
    (Pulled.LineBilinear.fiberComparison q L y (y ≫ q) rfl).symm (D.unitFrame _ (FiberwiseMultiplicationPullback.imageUnit p q a ha)).hom
    (h T _ _ _ (FiberwiseMultiplicationPullback.imageUnit p q a ha) (FiberwiseMultiplicationPullback.imageRel p r q a x y hax) (FiberwiseMultiplicationPullback.imageRel p r q x a y hxa)) U m

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.FrameCentrality
