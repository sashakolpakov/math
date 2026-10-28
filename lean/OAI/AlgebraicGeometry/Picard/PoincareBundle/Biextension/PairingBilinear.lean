import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.FramePairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioMultiplication

/-! # Pairing Bilinear -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.PairingBilinear

noncomputable section

/-!
# Multiplicative kernel-intersection frames give a bilinear natural pairing

The hypotheses describe actual bilinear products of line fibers and their compatibility with the
two frames. Bilinearity of their ratio is proved, rather than included in the input data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.FramePairing OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioMultiplication

variable {S : Scheme.{u}} {H K : Over S} [GrpObj H] [GrpObj K]
  (L : Line.Bundles.LineBundle (H ⊗ K).left)

/-- The two actual fiber products of the restricted biextension. -/
structure Products where
  leftProduct {T : Over S} (a a' : T ⟶ H) (b : T ⟶ K) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L (lift a b)) (Line.Fibers.fiber L (lift a' b)) (Line.Fibers.fiber L (lift (a * a') b))
  left_isIso {T : Over S} (a a' : T ⟶ H) (b : T ⟶ K) :
    IsIso (Bilinear.BilinearPullback.toHom (leftProduct a a' b))
  rightProduct {T : Over S} (a : T ⟶ H) (b b' : T ⟶ K) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L (lift a b)) (Line.Fibers.fiber L (lift a b')) (Line.Fibers.fiber L (lift a (b * b')))
  right_isIso {T : Over S} (a : T ⟶ H) (b b' : T ⟶ K) :
    IsIso (Bilinear.BilinearPullback.toHom (rightProduct a b b'))

/-- A frame respects both products on the actual pulled-back line sheaves. -/
def IsMultiplicativeFrame (P : Products L) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ K).left ≅ L.sheaf) : Prop :=
  (∀ (T : Over S) (a a' : T ⟶ H) (b : T ⟶ K) (U : T.left.Opens),
    (P.leftProduct a a' b).app U ((FramePairing.testFrame L s a b).hom.app U (1 : Γ(T.left, U)))
      ((FramePairing.testFrame L s a' b).hom.app U (1 : Γ(T.left, U))) =
        (FramePairing.testFrame L s (a * a') b).hom.app U (1 : Γ(T.left, U))) ∧
  (∀ (T : Over S) (a : T ⟶ H) (b b' : T ⟶ K) (U : T.left.Opens),
    (P.rightProduct a b b').app U ((FramePairing.testFrame L s a b).hom.app U (1 : Γ(T.left, U)))
      ((FramePairing.testFrame L s a b').hom.app U (1 : Γ(T.left, U))) =
        (FramePairing.testFrame L s a (b * b')).hom.app U (1 : Γ(T.left, U)))

variable (P : Products L) (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ K).left ≅ L.sheaf)
  (hs : IsMultiplicativeFrame L P s) (ht : IsMultiplicativeFrame L P t)

include hs ht in
/-- Multiplication in the first kernel variable multiplies the obstruction values. -/
theorem pairingValue_mul_left {T : Over S} (a a' : T ⟶ H) (b : T ⟶ K) :
    FramePairing.pairingValue L s t (a * a') b = FramePairing.pairingValue L s t a b * FramePairing.pairingValue L s t a' b :=
  FrameRatioMultiplication.frameRatio_product (P.leftProduct a a' b) _ _ _ _ _ _ (hs.1 T a a' b ⊤) (ht.1 T a a' b ⊤)

include hs ht in
/-- Multiplication in the second kernel variable multiplies the obstruction values. -/
theorem pairingValue_mul_right {T : Over S} (a : T ⟶ H) (b b' : T ⟶ K) :
    FramePairing.pairingValue L s t a (b * b') = FramePairing.pairingValue L s t a b * FramePairing.pairingValue L s t a b' :=
  FrameRatioMultiplication.frameRatio_product (P.rightProduct a b b') _ _ _ _ _ _ (hs.2 T a b b' ⊤) (ht.2 T a b b' ⊤)

/-- The two multiplicative frames construct a genuine bilinear pairing on all scheme-valued points. -/
def pairing (T : Over S) : (T ⟶ H) →* (T ⟶ K) →* Γ(T.left, ⊤)ˣ :=
  MonoidHom.mk' (fun a => MonoidHom.mk' (FramePairing.pairingValue L s t a)
    (pairingValue_mul_right L P s t hs ht a)) (fun a a' => by
      apply MonoidHom.ext
      intro b
      exact pairingValue_mul_left L P s t hs ht a a' b)

/-- The resulting bilinear pairing is natural for arbitrary, possibly nonreduced, test schemes. -/
theorem pairing_naturality {T T' : Over S} (g : T' ⟶ T) (a : T ⟶ H) (b : T ⟶ K) :
    pairing L P s t hs ht T' (g ≫ a) (g ≫ b) =
      Units.map g.left.appTop.hom (pairing L P s t hs ht T a b) :=
  FramePairing.pairingValue_naturality L s t g a b

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.PairingBilinear
