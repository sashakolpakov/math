import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Closed Immersion Module Epi -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ClosedImmersionModuleEpi.Construction

noncomputable section

/-! A closed immersion gives a quotient of the actual structure sheaf as a module sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem moduleMap_epi_of_affine_sections_surjective
    {X : Scheme.{u}} {M N : X.Modules} (a : M ⟶ N)
    (ha : ∀ U : X.affineOpens, Function.Surjective (a.app U.1)) : Epi a := by
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
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨Z.presheaf, Z.isSheaf⟩
  apply F.eq_of_locally_eq' (fun x => (V x).1) U.unop
    (fun x => homOfLE (hVU x))
    (by intro x hxU; exact Opens.mem_iSup.mpr ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩)
  intro x
  let j := (homOfLE (hVU x)).op
  obtain ⟨r, hr⟩ := ha (V x) (N.presheaf.map j s)
  have hh := congrArg (fun k : M ⟶ Z => k.app (V x).1 r) he
  change g.app (V x).1 (a.app (V x).1 r) = h.app (V x).1 (a.app (V x).1 r) at hh
  rw [hr] at hh
  exact (PresheafOfModules.naturality_apply g.val j s).symm.trans
    (hh.trans (PresheafOfModules.naturality_apply h.val j s))

theorem closedImmersion_structureModule_epi
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    Epi (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  apply moduleMap_epi_of_affine_sections_surjective
  intro U
  exact f.app_surjective U.1 U.2

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ClosedImmersionModuleEpi.Construction
