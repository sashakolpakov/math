import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Map Basis Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapBasisExtension

noncomputable section

/-! Compatible linear maps on a topological basis extend to actual module-sheaf maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v

variable {X : Scheme.{u}} {ι : Type v} (B : ι → X.Opens) (M N : X.Modules)

structure ModuleBasisMap where
  app : ∀ i, Γ(M, B i) →ₗ[Γ(X, B i)] Γ(N, B i)
  naturality : ∀ i j (h : B i ≤ B j) (s : Γ(M, B j)),
    app i (M.presheaf.map (homOfLE h).op s) =
      N.presheaf.map (homOfLE h).op (app j s)

namespace ModuleBasisMap

variable {B M N} (D : ModuleBasisMap B M N)

def presheafMap :
    (inducedFunctor B).op ⋙ M.presheaf ⟶ (inducedFunctor B).op ⋙ N.presheaf where
  app i := AddCommGrpCat.ofHom (D.app i.unop).toAddMonoidHom
  naturality {i j} h := by
    apply ConcreteCategory.hom_ext
    intro s
    exact D.naturality j.unop i.unop h.unop.hom.le s

variable (hB : Opens.IsBasis (Set.range B))

def extendedPresheafMap : M.presheaf ⟶ N.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB D.presheafMap

theorem extendedPresheafMap_app (i : ι) (s : Γ(M, B i)) :
    (D.extendedPresheafMap hB).app (.op (B i)) s = D.app i s := by
  exact ConcreteCategory.congr_hom
    (TopCat.Sheaf.extend_hom_app M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB D.presheafMap i) s

theorem extendedPresheafMap_smul (U : X.Opens) (r : Γ(X, U)) (s : Γ(M, U)) :
    (D.extendedPresheafMap hB).app (.op U) (r • s) =
      r • (D.extendedPresheafMap hB).app (.op U) s := by
  apply N.isSheaf.section_ext
  intro x hx
  obtain ⟨V, ⟨i, rfl⟩, hxi, hi⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨B i, hi, hxi, ?_⟩
  have hn (z : Γ(M, U)) :
      N.presheaf.map (homOfLE hi).op ((D.extendedPresheafMap hB).app (.op U) z) =
        D.app i (M.presheaf.map (homOfLE hi).op z) :=
    (ConcreteCategory.congr_hom ((D.extendedPresheafMap hB).naturality (homOfLE hi).op) z).symm.trans
      (D.extendedPresheafMap_app hB i _)
  rw [hn, Scheme.Modules.map_smul, Scheme.Modules.map_smul, hn, map_smul]

def extend : M ⟶ N where
  val := {
    app U := ModuleCat.ofHom {
      toFun := (D.extendedPresheafMap hB).app U
      map_add' := map_add ((D.extendedPresheafMap hB).app U).hom
      map_smul' := D.extendedPresheafMap_smul hB U.unop }
    naturality h := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      exact ConcreteCategory.congr_hom ((D.extendedPresheafMap hB).naturality h) s }

theorem extend_app (i : ι) (s : Γ(M, B i)) : (D.extend hB).app (B i) s = D.app i s :=
  D.extendedPresheafMap_app hB i s

end ModuleBasisMap

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapBasisExtension
