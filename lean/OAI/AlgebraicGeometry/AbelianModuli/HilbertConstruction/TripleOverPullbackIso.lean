import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Triple Over Pullback Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TripleOverPullbackIso

noncomputable section

/-! Three successive pullbacks are naturally the pullback along their composite. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

def tripleOverPullbackIso
    {C : Type u} [Category.{v} C] [HasPullbacks C] {S T U V : C}
    (f : T ⟶ S) (g : U ⟶ T) (h : V ⟶ U) (k : V ⟶ S) (hk : (h ≫ g) ≫ f = k)
    (X : Over S) :
    (Over.pullback h).obj ((Over.pullback g).obj ((Over.pullback f).obj X)) ≅
      (Over.pullback k).obj X :=
  (Over.pullbackComp h g).symm.app ((Over.pullback f).obj X) ≪≫
    (Over.pullbackComp (h ≫ g) f).symm.app X ≪≫
      eqToIso (congrArg (fun a : V ⟶ S => (Over.pullback a).obj X) hk)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TripleOverPullbackIso
