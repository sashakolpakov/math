import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SectionGlobalValue
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ScalarSectionGlobalValue
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.ModuleTensorComparison

/-! # Tensor Section Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.TensorSectionValues

noncomputable section

/-! Over a changed-base field, pure tensors in the canonical comparison are the global values of coefficient multiples of actual pulled-back sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem fieldTensorComparison_sectionValue
    {K : Type u} [Field K] {S X P : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Spec (.of K)} {f : X ⟶ S} {g : Spec (.of K) ⟶ S}
    (H : IsPullback a b f g) (M : X.Modules) (c : Affine.TensorSectionComparison.morphismGlobalAlgebra g)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).obj (.op ⊤)) :
    (show Γ((Scheme.Modules.pullback a).obj M, ⊤) from
      (Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (.op ⊤) (c ⊗ₜ[Γ(S, ⊤)] x)) =
      Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M)
        (Coefficient.ScalarSections.coefficientScalarSection b ((Scheme.ΓSpecIso (.of K)).hom c)
          (Ample.LineBundles.pullbackSection a ((Global.Sections.moduleSectionHomEquiv M).symm x))) := by
  have hv := (Pullback.SectionGlobalValue.pullbackSection_globalValue a ((Global.Sections.moduleSectionHomEquiv M).symm x)).trans
    (congrArg (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤)
      ((Global.Sections.moduleSectionHomEquiv M).apply_symm_apply x))
  have hs := (ScalarSectionGlobalValue.coefficientScalarSection_globalValue b ((Scheme.ΓSpecIso (.of K)).hom c)
      (Ample.LineBundles.pullbackSection a ((Global.Sections.moduleSectionHomEquiv M).symm x))).trans
    (congrArg₂ (fun (r : Γ(P, ⊤)) (v : Γ((Scheme.Modules.pullback a).obj M, ⊤)) => r • v)
      (ScalarSectionGlobalValue.schemeCoefficientMap_globalValue b c) hv)
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

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.TensorSectionValues
