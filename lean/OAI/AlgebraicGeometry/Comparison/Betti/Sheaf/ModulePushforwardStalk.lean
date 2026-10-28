import OAI.AlgebraicGeometry.Comparison.Betti.Module.RingedStalkPushforward
import OAI.AlgebraicGeometry.Comparison.Betti.StalkPointModuleAdjunction
import Mathlib.CategoryTheory.Whiskering

/-! # Module Pushforward Stalk -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ModulePushforwardStalk.Local

noncomputable section

/-! The normalized module pushforward stalk isomorphism for native sheaves of modules. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}
  {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{0}}
  [(Opens.map f).IsContinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)]
  (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R) (x : X)

def sheafModulePushforwardStalkIso (hf : Topology.IsInducing f) :
    SheafOfModules.pushforward φ ⋙ StalkPointModuleAdjunction.Local.sheafRingModuleStalk S (f x) ≅
      StalkPointModuleAdjunction.Local.sheafRingModuleStalk R x ⋙ ModuleCat.restrictScalars (Module.RingedStalkPushforward.Local.ringedStalkMap f φ.hom x) :=
  Functor.isoWhiskerLeft (SheafOfModules.forget R) (Module.RingedStalkPushforward.Local.modulePushforwardStalkIso f φ.hom x hf)

theorem sheafModulePushforwardStalkIso_germ (hf : Topology.IsInducing f)
    (M : SheafOfModules.{0} R) (U : Opens Y) (hx : f x ∈ U)
    (m : ((SheafOfModules.pushforward φ).obj M).val.obj (op U)) :
    (sheafModulePushforwardStalkIso f φ x hf).hom.app M
      (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := Y)
        ((SheafOfModules.pushforward φ).obj M).val.presheaf U (f x) hx m) =
    TopCat.Presheaf.germ (C := AddCommGrpCat) (X := X) M.val.presheaf
      ((Opens.map f).obj U) x hx m :=
  Module.RingedStalkPushforward.Local.modulePushforwardStalkIso_germ f φ.hom x hf M.val U hx m

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ModulePushforwardStalk.Local
