import Mathlib.Algebra.Category.Grp.Zero
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.StalkExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.Annihilator

/-! # Stalk Support Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.StalkSupportTransport

noncomputable section

/-! Nonzero actual module stalks lie in the coherent support. A direct
image along an inducing scheme map has the same additive stalk at the
corresponding point, including for closed immersions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

attribute [local instance] StalkExactness.moduleStalkUnderlying_additive

theorem moduleStalk_isZero_iff_additive {X : Scheme.{u}} (M : X.Modules) (x : X) :
    IsZero ((StalkExactness.moduleStalkFunctor x).obj M) ↔ IsZero (M.presheaf.stalk x) :=
  ModuleCat.isZero_iff_subsingleton.trans (AddCommGrpCat.isZero_iff_subsingleton (G := M.presheaf.stalk x)).symm

def modulePushforwardStalkAddIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Topology.IsInducing f) (M : X.Modules) (x : X) :
    ((Scheme.Modules.pushforward f).obj M).presheaf.stalk (f x) ≅ M.presheaf.stalk x := by
  have hg : IsIso (M.presheaf.stalkPushforward AddCommGrpCat.{u} f.base x) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u} hf M.presheaf x
  exact @asIso _ _ _ _ (M.presheaf.stalkPushforward AddCommGrpCat.{u} f.base x) hg

theorem modulePushforward_stalk_isZero_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Topology.IsInducing f) (M : X.Modules) (x : X) :
    IsZero ((StalkExactness.moduleStalkFunctor (f x)).obj ((Scheme.Modules.pushforward f).obj M)) ↔
      IsZero ((StalkExactness.moduleStalkFunctor x).obj M) := by
  rw [moduleStalk_isZero_iff_additive, moduleStalk_isZero_iff_additive]
  exact (modulePushforwardStalkAddIso f hf M x).isZero_iff

theorem nonzero_moduleStalk_mem_coherent_support {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (x : X)
    (hx : ¬ IsZero ((StalkExactness.moduleStalkFunctor x).obj M)) : x ∈ (Coherent.Annihilator.coherentAnnihilator M).support := by
  apply (Coherent.Annihilator.coherentAnnihilator_mem_support_iff M x).mpr
  intro hvan
  obtain ⟨U, hxU, hU⟩ := (VanishingOpen.mem_moduleVanishingOpen M x).mp hvan
  let y : U.toScheme := ⟨x, hxU⟩
  let F := Scheme.Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  let e := (Scheme.Modules.restrictStalkNatIso U.ι y).app M
  apply hx
  apply (moduleStalk_isZero_iff_additive M x).mpr
  exact e.isZero_iff.mp (F.map_isZero hU)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.StalkSupportTransport
