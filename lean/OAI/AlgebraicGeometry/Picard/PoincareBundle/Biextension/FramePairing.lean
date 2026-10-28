import OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

/-! # Frame Pairing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.FramePairing

noncomputable section

/-!
# The natural pairing obtained by comparing two kernel-intersection frames

The values are units in the actual ring of functions of every test scheme. In particular, the
construction retains infinitesimal test schemes and does not replace a kernel by geometric points.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback

variable {S : Scheme.{u}} {H K : Over S} (L : Line.Bundles.LineBundle (H ⊗ K).left)
  (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ K).left ≅ L.sheaf)

/-- A global frame on the kernel product restricts to each actual pair of test points. -/
def testFrame {T : Over S} (a : T ⟶ H) (b : T ⟶ K) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L (lift a b) :=
  FrameRatioPullback.pullFrame (lift a b).left s

/-- The obstruction at a pair of scheme-valued kernel points is the ratio of the two frames. -/
def pairingValue {T : Over S} (a : T ⟶ H) (b : T ⟶ K) : Γ(T.left, ⊤)ˣ :=
  Line.FrameUnits.frameRatio (testFrame L s a b) (testFrame L t a b)

/-- The test-point obstruction is the pullback of one genuine invertible function on the product. -/
theorem pairingValue_eq {T : Over S} (a : T ⟶ H) (b : T ⟶ K) :
    pairingValue L s t a b = Units.map (lift a b).left.appTop.hom (Line.FrameUnits.frameRatio s t) :=
  FrameRatioPullback.frameRatio_pullFrame (lift a b).left s t

/-- Naturality holds for every map of test schemes, with the genuine ring map on functions. -/
theorem pairingValue_naturality {T T' : Over S} (g : T' ⟶ T) (a : T ⟶ H) (b : T ⟶ K) :
    pairingValue L s t (g ≫ a) (g ≫ b) = Units.map g.left.appTop.hom (pairingValue L s t a b) := by
  rw [pairingValue_eq, pairingValue_eq, ← comp_lift]
  change Units.map (g.left ≫ (lift a b).left).appTop.hom.toMonoidHom (Line.FrameUnits.frameRatio s t) = _
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- Triviality on all scheme-valued pairs is equivalent to equality of the actual global frames. -/
theorem pairingValue_all_one_iff :
    (∀ (T : Over S) (a : T ⟶ H) (b : T ⟶ K), pairingValue L s t a b = 1) ↔ s = t := by
  constructor
  · intro h
    have hp := h (H ⊗ K) (fst H K) (snd H K)
    rw [pairingValue_eq, lift_fst_snd] at hp
    change Units.map ((𝟙 (H ⊗ K).left) : (H ⊗ K).left ⟶ (H ⊗ K).left).appTop.hom.toMonoidHom
      (Line.FrameUnits.frameRatio s t) = 1 at hp
    rw [Scheme.Hom.id_appTop] at hp
    exact (Line.FrameUnits.frameRatio_eq_one_iff s t).mp hp
  · rintro rfl T a b
    exact (Line.FrameUnits.frameRatio_eq_one_iff _ _).mpr rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.FramePairing
