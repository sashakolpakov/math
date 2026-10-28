import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapLocalFactor

/-! # Map Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapValues

noncomputable section

/-! Read a module map on an open subscheme as compatible linear maps on smaller ambient opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

theorem moduleRestrictionUnit_app_isIso (M : Y.Modules) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app U) := by
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  have he : f ''ᵁ f ⁻¹ᵁ U = U :=
    (f.image_preimage_eq_opensRange_inf U).trans (inf_eq_right.mpr hU)
  have : IsIso (homOfLE (f.image_preimage_le U)) := homOfLE_isIso_of_eq _ he
  exact M.presheaf.map_isIso _

variable {M N : Y.Modules}

def openModuleMapValue (φ : M.restrict f ⟶ N.restrict f) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    Γ(M, U) →ₗ[Γ(Y, U)] Γ(N, U) := by
  letI := moduleRestrictionUnit_app_isIso f N U hU
  exact Module.MapLocalFactor.moduleMapLocalFactor
    ((Scheme.Modules.restrictAdjunction f).unit.app M ≫ (Scheme.Modules.pushforward f).map φ)
    ((Scheme.Modules.restrictAdjunction f).unit.app N) U

theorem openModuleMapValue_natural (φ : M.restrict f ⟶ N.restrict f)
    {U V : Y.Opens} (h : V ≤ U) (hU : U ≤ f.opensRange) (hV : V ≤ f.opensRange)
    (s : Γ(M, U)) :
    openModuleMapValue f φ V hV (M.presheaf.map (homOfLE h).op s) =
      N.presheaf.map (homOfLE h).op (openModuleMapValue f φ U hU s) := by
  let := moduleRestrictionUnit_app_isIso f N U hU
  let := moduleRestrictionUnit_app_isIso f N V hV
  exact Module.MapLocalFactor.moduleMapLocalFactor_natural _ _ h s

theorem openModuleMapValue_from_global (φ : M ⟶ N) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    openModuleMapValue f ((Scheme.Modules.restrictFunctor f).map φ) U hU =
      Tensor.Powers.SheafMultilinearMap.homApp φ U := by
  let := moduleRestrictionUnit_app_isIso f N U hU
  apply Eq.symm
  apply Module.MapLocalFactor.moduleMapLocalFactor_unique
  intro s
  have h := congrArg (fun ψ : M ⟶ (Scheme.Modules.pushforward f).obj (N.restrict f) => ψ.app U)
    ((Scheme.Modules.restrictAdjunction f).unit.naturality φ)
  exact ConcreteCategory.congr_hom h s

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapValues
