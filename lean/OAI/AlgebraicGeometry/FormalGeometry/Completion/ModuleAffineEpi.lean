import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Module Affine Epi -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ModuleAffineEpi

noncomputable section

/-! Surjectivity on affine sections detects actual epimorphisms of module sheaves. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

namespace Construction

universe u

theorem moduleHom_ext_of_affine {X : Scheme.{u}} {M N : X.Modules} (a b : M ⟶ N)
    (h : ∀ U : X.affineOpens, a.app U.1 = b.app U.1) : a = b := by
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
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨N.presheaf, N.isSheaf⟩
  apply F.eq_of_locally_eq' (fun x => (V x).1) U.unop
    (fun x => homOfLE (hVU x))
    (by intro x hxU; exact Opens.mem_iSup.mpr ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩)
  intro x
  let j := (homOfLE (hVU x)).op
  exact (PresheafOfModules.naturality_apply a.val j s).symm.trans
    ((ConcreteCategory.congr_hom (h (V x)) (M.presheaf.map j s)).trans
      (PresheafOfModules.naturality_apply b.val j s))

theorem moduleMap_epi_of_affine_sections_surjective {X : Scheme.{u}} {M N : X.Modules}
    (a : M ⟶ N) (ha : ∀ U : X.affineOpens, Function.Surjective (a.app U.1)) : Epi a := by
  constructor
  intro Z g h he
  apply moduleHom_ext_of_affine
  intro U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro y
  obtain ⟨x, rfl⟩ := ha U y
  exact congrArg (fun t : M ⟶ Z => t.app U.1 x) he

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ModuleAffineEpi
