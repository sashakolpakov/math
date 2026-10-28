import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapBasisExtension

/-! # Presheaf Module Basis Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafModuleBasisMaps

noncomputable section

/-! Compatible linear maps from an arbitrary module presheaf on a topological basis extend uniquely to a sheaf target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v

variable {X : Scheme.{u}} {ι : Type v} (B : ι → X.Opens) (P : X.PresheafOfModules) (N : X.Modules)

local instance (V : X.Opens) : Module Γ(X, V) (P.obj (.op V)) :=
  (P.obj (.op V)).isModule

structure PresheafModuleBasisMap where
  app : ∀ i, P.obj (.op (B i)) →ₗ[Γ(X, B i)] Γ(N, B i)
  naturality : ∀ i j (h : B i ≤ B j) (s : P.obj (.op (B j))),
    app i (P.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (app j s)

namespace PresheafModuleBasisMap

variable {B P N} (D : PresheafModuleBasisMap B P N)

def presheafMap :
    (inducedFunctor B).op ⋙ P.presheaf ⟶ (inducedFunctor B).op ⋙ N.presheaf where
  app i := AddCommGrpCat.ofHom (D.app i.unop).toAddMonoidHom
  naturality {i j} h := by
    apply ConcreteCategory.hom_ext
    intro s
    exact D.naturality j.unop i.unop h.unop.hom.le s

variable (hB : Opens.IsBasis (Set.range B))

def extendedPresheafMap : P.presheaf ⟶ N.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom P.presheaf ⟨N.presheaf, N.isSheaf⟩ hB D.presheafMap

theorem extendedPresheafMap_app (i : ι) (s : P.obj (.op (B i))) :
    (D.extendedPresheafMap hB).app (.op (B i)) s = D.app i s :=
  ConcreteCategory.congr_hom
    (TopCat.Sheaf.extend_hom_app P.presheaf ⟨N.presheaf, N.isSheaf⟩ hB D.presheafMap i) s

theorem extendedPresheafMap_smul (V : X.Opens) (r : Γ(X, V)) (s : P.obj (.op V)) :
    (D.extendedPresheafMap hB).app (.op V) (r • s) = r • (D.extendedPresheafMap hB).app (.op V) s := by
  apply N.isSheaf.section_ext
  intro x hx
  obtain ⟨W, ⟨i, rfl⟩, hxi, hi⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨B i, hi, hxi, ?_⟩
  have hn (z : P.obj (.op V)) :
      N.presheaf.map (homOfLE hi).op ((D.extendedPresheafMap hB).app (.op V) z) =
        D.app i (P.map (homOfLE hi).op z) :=
    (ConcreteCategory.congr_hom ((D.extendedPresheafMap hB).naturality (homOfLE hi).op) z).symm.trans
      (D.extendedPresheafMap_app hB i _)
  rw [hn, Scheme.Modules.map_smul, hn]
  exact (congrArg (D.app i) (P.map_smul (homOfLE hi).op r s)).trans ((D.app i).map_smul _ _)

def extend : P ⟶ N.val :=
  PresheafOfModules.homMk (D.extendedPresheafMap hB) (fun V r s => D.extendedPresheafMap_smul hB V.unop r s)

theorem extend_app (i : ι) (s : P.obj (.op (B i))) :
    (D.extend hB).app (.op (B i)) s = D.app i s :=
  D.extendedPresheafMap_app hB i s

end PresheafModuleBasisMap

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafModuleBasisMaps
