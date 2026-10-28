import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientCechTensor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FactorSheafNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleScalars

/-! # Ambient Section Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientSectionScalars

noncomputable section

/-! The native ambient section pairing respects the original coefficient
scalar action on the external tensor sheaf. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y P : Scheme.{u}} {R : Type u} [CommRing R]
variable (a : P ⟶ X) (b : P ⟶ Y) (cX : R →+* Γ(X, ⊤)) (cY : R →+* Γ(Y, ⊤))
variable (hc : a.appTop.hom.comp cX = b.appTop.hom.comp cY) (M : X.Modules) (N : Y.Modules)

theorem nativeAmbientExternalSectionMap_scalar
    (V : X.Opens) (U : Y.Opens) (r : R)
    (z : TensorProduct R ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U))
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj (op V))) :
    (Open.FactorSheafNaturality.IntrinsicCech.cechOpenFactorMap
      (UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom (Global.ModuleScalars.globalModuleScalar
        (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N))
        ((a.appTop.hom.comp cX) r))) (b ⁻¹ᵁ U)).hom.app (op (a ⁻¹ᵁ V))
      ((AmbientExternalPresheafMap.nativeAmbientExternalSectionMap a b cX cY hc M N U).app (op V) z) =
    (AmbientExternalPresheafMap.nativeAmbientExternalSectionMap a b cX cY hc M N U).app (op V) (r • z) := by
  let E := Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N)
  let F := UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf E
  let s := UnderlyingAdditiveSheafExactness.ModuleSheaf.Hom.sheafHom (Global.ModuleScalars.globalModuleScalar E ((a.appTop.hom.comp cX) r))
  let σ := (AmbientExternalPresheafMap.nativeAmbientExternalSectionMap a b cX cY hc M N U).app (op V)
  let ρ := (Open.FactorSheafNaturality.IntrinsicCech.cechOpenFactorMap s (b ⁻¹ᵁ U)).hom.app (op (a ⁻¹ᵁ V))
  let e := Cech.SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso F (b ⁻¹ᵁ U) (a ⁻¹ᵁ V)
  let β := AmbientExternalSectionPairing.ambientExternalSectionTensorMap a b cX cY hc M N V U
  have hβ (x : TensorProduct R ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U))
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj (op V))) : e.hom (σ x) = β x :=
    ConcreteCategory.congr_hom (AmbientAffinePairing.nativeAmbientExternalSectionMap_comparison a b cX cY hc M N V U) x
  have hn : e.hom (ρ (σ z)) = s.hom.app (op (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ U)) (e.hom (σ z)) :=
    ConcreteCategory.congr_hom
      (Open.FactorSheafNaturality.IntrinsicCech.cechOpenFactorSectionsIso_sheaf_naturality s (b ⁻¹ᵁ U) (a ⁻¹ᵁ V)) (σ z)
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  change e.hom (ρ (σ z)) = e.hom (σ (r • z))
  calc
    _ = s.hom.app (op (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ U)) (e.hom (σ z)) := hn
    _ = s.hom.app (op (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ U)) (β z) := congrArg (fun t => s.hom.app (op (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ U)) t) (hβ z)
    _ = β (r • z) := by
      change r • β z = β (r • z)
      exact (β.map_smul r z).symm
    _ = _ := (hβ (r • z)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientSectionScalars
