import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.Nonvanishing
import Mathlib.Topology.Sheaves.Stalks

/-! # Module Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms

noncomputable section

/-! Local detection of isomorphisms of actual module sheaves on schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L M : X.Modules}

/-- A module-sheaf map that is invertible on a neighborhood of every point is invertible. -/
theorem moduleMap_isIso_of_locally (a : L ⟶ M)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIso ((Scheme.Modules.pullback U.ι).map a)) :
    IsIso a := by
  have hs (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map a.mapPresheaf) := by
    obtain ⟨U, hx, hU⟩ := h x
    have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map a) :=
      (Power.Nonvanishing.isIso_restrict_map_iff U.ι a).mpr hU
    let y : U.toScheme := ⟨x, hx⟩
    let e := Scheme.Modules.restrictStalkNatIso U.ι y
    have ht : IsIso (((Scheme.Modules.toPresheaf U.toScheme) ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          ((Scheme.Modules.restrictFunctor U.ι).map a)) :=
      Functor.map_isIso _ _
    have he : IsIso (((Scheme.Modules.restrictFunctor U.ι) ⋙
        Scheme.Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map a) ↔
        IsIso (((Scheme.Modules.toPresheaf X) ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.ι y)).map a) := by
      have hn := congrArg (fun z => IsIso z) (e.hom.naturality a)
      simpa only [isIso_comp_right_iff, isIso_comp_left_iff] using hn.to_iff
    exact he.mp ht
  let b : (⟨L.presheaf, L.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
      (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := ⟨a.mapPresheaf⟩
  have hb : IsIso b := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso b
  have hb' : IsIso ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map b) :=
    @Functor.map_isIso _ _ _ _ _ _ (TopCat.Sheaf.forget AddCommGrpCat.{u} X) b hb
  have : IsIso ((Scheme.Modules.toPresheaf X).map a) := hb'
  exact isIso_of_reflects_iso a (Scheme.Modules.toPresheaf X)

/-- Local invertibility and global invertibility are equivalent for module-sheaf maps. -/
theorem moduleMap_isIso_iff_locally (a : L ⟶ M) :
    IsIso a ↔ ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIso ((Scheme.Modules.pullback U.ι).map a) := by
  constructor
  · intro ha x
    let := ha
    exact ⟨⊤, trivial, (Scheme.Modules.pullback (⊤ : X.Opens).ι).map_isIso a⟩
  · exact moduleMap_isIso_of_locally a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms
