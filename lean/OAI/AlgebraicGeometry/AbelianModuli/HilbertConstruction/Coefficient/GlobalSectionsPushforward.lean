import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsFunctor

/-! # Global Sections Pushforward -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsPushforward

noncomputable section

/-! Direct image preserves actual global sections with their structural coefficient action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]

theorem schemeCoefficientMap_comp (f : X ⟶ Y) (p : Y ⟶ Spec (.of R)) :
    ModulePresheaf.schemeCoefficientMap (f ≫ p) = f.appTop.hom.comp (ModulePresheaf.schemeCoefficientMap p) := by
  ext r
  rfl

def schemeGlobalSectionsPushforwardIso (f : X ⟶ Y) (p : Y ⟶ Spec (.of R)) (M : X.Modules) :
    (GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj ((Scheme.Modules.pushforward f).obj M) ≃ₗ[R]
      (GlobalSectionsFunctor.schemeGlobalSectionsFunctor (f ≫ p)).obj M where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    change (M.smul (f.appTop (Y.presheaf.map (𝟙 (.op (⊤ : Y.Opens)))
      (ModulePresheaf.schemeCoefficientMap p r)))).hom m =
      (M.smul (X.presheaf.map (𝟙 (.op (⊤ : X.Opens)))
        (ModulePresheaf.schemeCoefficientMap (f ≫ p) r))).hom m
    apply congrArg (fun z : Γ(X, ⊤) => (M.smul z).hom m)
    have hy : Y.presheaf.map (𝟙 (.op (⊤ : Y.Opens))) (ModulePresheaf.schemeCoefficientMap p r) =
        ModulePresheaf.schemeCoefficientMap p r := ConcreteCategory.congr_hom (Y.presheaf.map_id _) _
    have hx : X.presheaf.map (𝟙 (.op (⊤ : X.Opens))) (ModulePresheaf.schemeCoefficientMap (f ≫ p) r) =
        ModulePresheaf.schemeCoefficientMap (f ≫ p) r := ConcreteCategory.congr_hom (X.presheaf.map_id _) _
    exact (congrArg f.appTop hy).trans
      ((DFunLike.congr_fun (schemeCoefficientMap_comp f p) r).symm.trans hx.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsPushforward
