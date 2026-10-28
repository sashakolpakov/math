import OAI.AlgebraicGeometry.SheafCohomology.Projective.LinearHom
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Module Hom Gluing -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHomGluing

noncomputable section

/-! Gluing compatible local module maps on a covering family of opens. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace
universe u v

def linearHomLocalSection {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (f : M.over U ⟶ N.over U) : (LinearHom.linearHomSheaf X.ringCatSheaf M N).obj.obj (.op U) :=
  ⟨LinearHom.linearHomToAmbient X.ringCatSheaf M N U f, ⟨f, rfl⟩⟩

def typeSectionsOfTop {X : TopCat.{u}} (F : X.Presheaf (Type u))
    (x : F.obj (.op ⊤)) : F.sections :=
  ⟨fun U => F.map U.unop.leTop.op x, fun {_ _} f => by
    rw [← F.map_comp_apply]
    congr 1⟩

theorem exists_moduleHom_of_compatible_localMaps {X : Scheme.{u}}
    (M N : X.Modules) {ι : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (f : ∀ i, M.over (U i) ⟶ N.over (U i))
    (hf : TopCat.Presheaf.IsCompatible
      (LinearHom.linearHomSheaf X.ringCatSheaf M N).obj U
      (fun i => linearHomLocalSection M N (U i) (f i))) :
    ∃ g : M ⟶ N, ∀ i, g.over (U i) = f i := by
  let F : TopCat.Sheaf (Type u) X := LinearHom.linearHomSheaf X.ringCatSheaf M N
  obtain ⟨x, hx, _⟩ := F.existsUnique_gluing' U ⊤ (fun i => (U i).leTop)
    (by rw [hU]) (fun i => linearHomLocalSection M N (U i) (f i)) hf
  let s := typeSectionsOfTop F.obj x
  let g := LinearHom.moduleHomOfSections X.ringCatSheaf M N s
  refine ⟨g, fun i => ?_⟩
  apply (_root_.SheafOfModules.toSheaf (X.ringCatSheaf.over (U i))).map_injective
  have hi := LinearHom.moduleHomOfSections_over X.ringCatSheaf M N s (U i)
  have hs := congrArg Subtype.val (hx i)
  exact hi.trans hs

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHomGluing
