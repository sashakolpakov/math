import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SectionGlobalValue
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.ModuleTensorComparison

/-! # Scalar Section Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ScalarSectionValues

noncomputable section

/-! Pure tensors in the canonical comparison are global values of actual sections multiplied by functions from the changed base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem tensorComparison_scalarSectionValue
    {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (M : X.Modules) (c : Affine.TensorSectionComparison.morphismGlobalAlgebra g)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).obj (.op ⊤)) :
    (show Γ((Scheme.Modules.pullback a).obj M, ⊤) from
      (Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (.op ⊤) (c ⊗ₜ[Γ(S, ⊤)] x)) =
      Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M)
        (Scalar.SectionValues.scalarSection (b.appTop c) (Ample.LineBundles.pullbackSection a ((Global.Sections.moduleSectionHomEquiv M).symm x))) := by
  have hv := (Pullback.SectionGlobalValue.pullbackSection_globalValue a ((Global.Sections.moduleSectionHomEquiv M).symm x)).trans
    (congrArg (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤)
      ((Global.Sections.moduleSectionHomEquiv M).apply_symm_apply x))
  have hs := (Scalar.SectionValues.scalarSection_globalValue (b.appTop c)
      (Ample.LineBundles.pullbackSection a ((Global.Sections.moduleSectionHomEquiv M).symm x))).trans
    (congrArg (fun v : Γ((Scheme.Modules.pullback a).obj M, ⊤) => b.appTop c • v) hv)
  have h := Module.TensorSectionValues.moduleSectionTensorComparisonApp_value (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
    a f.appTop.hom M b.appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) ⊤ c x
  change (show Γ((Scheme.Modules.pullback a).obj M, ⊤) from
      (Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (.op ⊤) (c ⊗ₜ[Γ(S, ⊤)] x)) =
    (P.presheaf.map (𝟙 (.op (⊤ : P.Opens))) (b.appTop c)) •
      (show Γ((Scheme.Modules.pullback a).obj M, ⊤) from
        ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤ x) at h
  have h' : (show Γ((Scheme.Modules.pullback a).obj M, ⊤) from
      (Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (.op ⊤) (c ⊗ₜ[Γ(S, ⊤)] x)) =
      b.appTop c • (show Γ((Scheme.Modules.pullback a).obj M, ⊤) from
        ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤ x) := by
    simpa only [P.presheaf.map_id, CommRingCat.id_apply] using h
  exact h'.trans hs.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ScalarSectionValues
