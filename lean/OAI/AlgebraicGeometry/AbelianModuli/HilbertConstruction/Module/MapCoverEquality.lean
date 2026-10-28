import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenMapGluing

/-! # Map Cover Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapCoverEquality

noncomputable section

/-! Equality of module-sheaf maps can be checked after restriction or canonical pullback on an open cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type v} (U : ι → X.Opens)
variable (hU : ∀ x : X, ∃ i, x ∈ U i)

include hU

theorem moduleMap_eq_of_restrict_cover (φ ψ : M ⟶ N)
    (h : ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).map φ =
      (Scheme.Modules.restrictFunctor (U i).ι).map ψ) : φ = ψ := by
  apply BasisIsomorphisms.moduleMap_eq_of_basis (OpenMapGluing.subordinateOpenBasis U) (OpenMapGluing.subordinateOpenBasis_isBasis U hU)
  intro V
  obtain ⟨i, hi⟩ := V.property
  have hv := congrArg (fun a => OpenMapGluing.moduleMapOnOpen (U i) a V.val hi) (h i)
  apply ConcreteCategory.hom_ext
  intro s
  have hφ : OpenMapGluing.moduleMapOnOpen (U i) ((Scheme.Modules.restrictFunctor (U i).ι).map φ) V.val hi s =
      φ.app V.val s := LinearMap.congr_fun (OpenModule.MapValues.openModuleMapValue_from_global (U i).ι φ V.val _) s
  have hψ : OpenMapGluing.moduleMapOnOpen (U i) ((Scheme.Modules.restrictFunctor (U i).ι).map ψ) V.val hi s =
      ψ.app V.val s := LinearMap.congr_fun (OpenModule.MapValues.openModuleMapValue_from_global (U i).ι ψ V.val _) s
  exact hφ.symm.trans ((LinearMap.congr_fun hv s).trans hψ)

theorem moduleMap_eq_of_pullback_cover (φ ψ : M ⟶ N)
    (h : ∀ i, (Scheme.Modules.pullback (U i).ι).map φ =
      (Scheme.Modules.pullback (U i).ι).map ψ) : φ = ψ := by
  apply moduleMap_eq_of_restrict_cover U hU
  intro i
  let E := Scheme.Modules.restrictFunctorIsoPullback (U i).ι
  apply (cancel_mono (E.app N).hom).mp
  exact (E.hom.naturality φ).trans
    ((congrArg (fun a => (E.app M).hom ≫ a) (h i)).trans (E.hom.naturality ψ).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapCoverEquality
