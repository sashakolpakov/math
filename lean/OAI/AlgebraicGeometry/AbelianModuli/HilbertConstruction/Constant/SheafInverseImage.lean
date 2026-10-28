import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Sheaf Inverse Image -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.SheafInverseImage

noncomputable section

/-! The inverse image of a constant abelian sheaf is constant, via the actual top-section adjunctions. Inverse image is additive and exact. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u

variable {X Y : TopCat.{u}}

def additivePushforwardTopIso (f : X ⟶ Y) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
      (sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj (op ⊤) ≅
    (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

def constantSheafInverseImageIso (f : X ⟶ Y) :
    constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⋙
      TopCat.Sheaf.pullback AddCommGrpCat.{u} f ≅
    constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  Adjunction.leftAdjointCompIso
    (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u} isTerminalTop)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop)
    (additivePushforwardTopIso f)

instance additiveSheafInverseImage_preservesFiniteLimits (f : X ⟶ Y) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) := by
  change PreservesFiniteLimits ((Opens.map f).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
  have : ReflectsLimits (forget AddCommGrpCat.{u}) :=
    reflectsLimits_of_reflectsIsomorphisms
  have : PreservesFiniteLimits
      ((Opens.map f).op.lan : ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})) :=
    lan_preservesFiniteLimits_of_flat AddCommGrpCat.{u} (Opens.map f)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits
    (Opens.map f) AddCommGrpCat.{u} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

instance additiveSheafInverseImage_additive (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).Additive :=
  Functor.additive_of_preserves_binary_products _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.SheafInverseImage
