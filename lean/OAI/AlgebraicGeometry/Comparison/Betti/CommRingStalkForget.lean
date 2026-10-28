import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # Comm Ring Stalk Forget -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Comparison.Betti.CommRingStalkForget.AnalyticLocal

/-! Forgetting commutativity preserves actual ring sheaf stalks and
their section germs, since the neighborhood colimit is filtered. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} (F : TopCat.Presheaf CommRingCat.{0} X) (x : X)

def commRingStalkForgetIso :
    (forget₂ CommRingCat RingCat).obj (F.stalk x) ≅
      TopCat.Presheaf.stalk (X := X) (F ⋙ forget₂ CommRingCat RingCat) x :=
  preservesColimitIso (forget₂ CommRingCat RingCat) ((OpenNhds.inclusion x).op ⋙ F)

theorem commRingStalkForgetIso_germ (U : Opens X) (hx : x ∈ U) :
    TopCat.Presheaf.germ (X := X) (F ⋙ forget₂ CommRingCat RingCat) U x hx ≫
      (commRingStalkForgetIso F x).inv =
      (forget₂ CommRingCat RingCat).map (F.germ U x hx) :=
  ι_preservesColimitIso_inv (forget₂ CommRingCat RingCat) ((OpenNhds.inclusion x).op ⋙ F) (op ⟨U, hx⟩)

def commRingStalkForgetEquiv :
    (TopCat.Presheaf.stalk (C := RingCat) (X := X) (F ⋙ forget₂ CommRingCat RingCat) x) ≃+* F.stalk x :=
  let i := (commRingStalkForgetIso F x).symm
  { i.hom.hom, ((forget RingCat).mapIso i).toEquiv with }

theorem commRingStalkForgetEquiv_germ (U : Opens X) (hx : x ∈ U) (f : F.obj (op U)) :
    commRingStalkForgetEquiv F x
      (TopCat.Presheaf.germ (X := X) (F ⋙ forget₂ CommRingCat RingCat) U x hx f) =
        F.germ U x hx f :=
  congrArg (fun k => k.hom f) (commRingStalkForgetIso_germ F x U hx)

end AlgebraicGeometry.Comparison.Betti.CommRingStalkForget.AnalyticLocal

namespace AlgebraicGeometry.Comparison.Betti.CommRingStalkForget.ModuleLocal

/-! A native RingCat stalk of a commutative-ring presheaf retains
commutative multiplication after forgetting the commutative structure. -/

open _root_.CategoryTheory

variable {X : TopCat.{0}} (R : TopCat.Presheaf CommRingCat.{0} X) (x : X)

instance commRingForgottenStalk_isMulCommutative :
    IsMulCommutative (TopCat.Presheaf.stalk (C := RingCat) (X := X)
      (R ⋙ forget₂ CommRingCat RingCat) x) :=
  ⟨⟨fun a b => (AnalyticLocal.commRingStalkForgetEquiv R x).injective
    (by rw [map_mul, map_mul, mul_comm])⟩⟩

end AlgebraicGeometry.Comparison.Betti.CommRingStalkForget.ModuleLocal

end

end OAI
