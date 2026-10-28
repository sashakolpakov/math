import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Module Map Local Mono -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ModuleMapLocalMono

noncomputable section

/-! Injectivity on affine sections detects actual monomorphisms of module sheaves. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Construction

universe u

theorem moduleMap_mono_of_nonempty_affine_sections_injective
    {X : Scheme.{u}} {M N : X.Modules} (a : M ⟶ N)
    (ha : ∀ U : X.affineOpens, (U.1 : Set X).Nonempty → Function.Injective (a.app U.1)) : Mono a := by
  constructor
  intro Z g h he
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  have hc (x : U.unop) : ∃ V : X.affineOpens, x.1 ∈ V.1 ∧ V.1 ≤ U.unop := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open x.2 U.unop.isOpen
    exact ⟨⟨V, hV⟩, hx, hVU⟩
  choose V hx hVU using hc
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
  apply F.eq_of_locally_eq' (fun x => (V x).1) U.unop
    (fun x => homOfLE (hVU x))
    (by intro x hxU; exact Opens.mem_iSup.mpr ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩)
  intro x
  let j := (homOfLE (hVU x)).op
  apply ha (V x) ⟨x.1, hx x⟩
  have hh := congrArg (fun k : Z ⟶ N => k.app (V x).1 (Z.presheaf.map j s)) he
  change a.app (V x).1 (g.app (V x).1 (Z.presheaf.map j s)) =
    a.app (V x).1 (h.app (V x).1 (Z.presheaf.map j s)) at hh
  exact (congrArg (a.app (V x).1) (PresheafOfModules.naturality_apply g.val j s)).symm.trans
    (hh.trans (congrArg (a.app (V x).1) (PresheafOfModules.naturality_apply h.val j s)))

theorem moduleMap_mono_of_affine_sections_injective
    {X : Scheme.{u}} {M N : X.Modules} (a : M ⟶ N)
    (ha : ∀ U : X.affineOpens, Function.Injective (a.app U.1)) : Mono a :=
  moduleMap_mono_of_nonempty_affine_sections_injective a (fun U _ => ha U)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ModuleMapLocalMono
