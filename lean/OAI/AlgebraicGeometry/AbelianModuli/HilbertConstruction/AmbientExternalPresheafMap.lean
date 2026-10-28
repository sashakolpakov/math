import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientExternalSectionPairing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientOpenFactorSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.CosimplicialForget

/-! # Ambient External Presheaf Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientExternalPresheafMap

noncomputable section

/-! The ambient tensor pairing maps into sections of the actual Cech open factor. Its parameter-restriction law is expressed using the native abelian-sheaf factor restriction, so no separate lift of that map to scheme modules is required. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

variable {X Y P : Scheme.{u}} {R : Type u} [CommRing R]
variable (a : P ⟶ X) (b : P ⟶ Y)
variable (cX : R →+* Γ(X, ⊤)) (cY : R →+* Γ(Y, ⊤))
variable (hc : a.appTop.hom.comp cX = b.appTop.hom.comp cY)
variable (M : X.Modules) (N : Y.Modules)

def ambientExternalTensorPresheafMap (U : Y.Opens) :
    Coefficient.ModulePresheaf.coefficientModulePresheaf cX M ⋙
      Module.TensorFunctor.ModuleTensorFunctor.tensor ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U)) ⟶
    (AmbientOpenFactorSections.ambientIntersectionOpenFunctor a (b ⁻¹ᵁ U)).op ⋙
      Coefficient.ModulePresheaf.coefficientModulePresheaf (a.appTop.hom.comp cX)
        (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N)) where
  app V := ModuleCat.ofHom
    (X := (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M ⋙
      Module.TensorFunctor.ModuleTensorFunctor.tensor ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U))).obj V)
    (Y := ((AmbientOpenFactorSections.ambientIntersectionOpenFunctor a (b ⁻¹ᵁ U)).op ⋙
      Coefficient.ModulePresheaf.coefficientModulePresheaf (a.appTop.hom.comp cX)
        (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N))).obj V)
    (AmbientExternalSectionPairing.ambientExternalSectionTensorMap a b cX cY hc M N V.unop U)
  naturality V W i := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro n m
    have h := AmbientExternalSectionPairing.ambientExternalSectionTensorMap_naturality a b cX cY hc M N
      (leOfHom i.unop) (show U ≤ U from le_rfl) n m
    have hid : (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).map
        (homOfLE (show U ≤ U from le_rfl)).op n = n := by
      change (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).map (𝟙 (op U)) n = n
      exact ConcreteCategory.congr_hom ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).map_id (op U)) n
    rw [hid] at h
    exact h

def nativeAmbientExternalSectionMap (U : Y.Opens) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M ⋙
      Module.TensorFunctor.ModuleTensorFunctor.tensor ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U))) ⋙ Module.ProductForget.moduleForget R ⟶
    AmbientOpenFactorSections.ambientOpenFactorSectionPresheaf a (b ⁻¹ᵁ U)
      (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
        ((Scheme.Modules.pullback b).obj N))) :=
  Functor.whiskerRight (ambientExternalTensorPresheafMap a b cX cY hc M N U) (Module.ProductForget.moduleForget R) ≫
    (Functor.associator (AmbientOpenFactorSections.ambientIntersectionOpenFunctor a (b ⁻¹ᵁ U)).op
      (Coefficient.ModulePresheaf.coefficientModulePresheaf (a.appTop.hom.comp cX)
        (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N)))
      (Module.ProductForget.moduleForget R)).hom ≫
    (Functor.isoWhiskerLeft (AmbientOpenFactorSections.ambientIntersectionOpenFunctor a (b ⁻¹ᵁ U)).op
      (CoefficientCech.CosimplicialForget.coefficientModulePresheafForgetIso (a.appTop.hom.comp cX)
        (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N)))).hom ≫
    (AmbientOpenFactorSections.ambientOpenFactorSectionsIso a (b ⁻¹ᵁ U)
      (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
        ((Scheme.Modules.pullback b).obj N)))).inv

theorem nativeAmbientExternalSectionMap_tmul (V : X.Opens) (U : Y.Opens)
    (n : (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U))
    (m : (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj (op V)) :
    (Cech.SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso
      (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
        ((Scheme.Modules.pullback b).obj N))) (b ⁻¹ᵁ U) (a ⁻¹ᵁ V)).hom
      ((nativeAmbientExternalSectionMap a b cX cY hc M N U).app (op V) (n ⊗ₜ[R] m)) =
        AmbientExternalSectionPairing.ambientExternalSectionTensorMap a b cX cY hc M N V U (n ⊗ₜ[R] m) := by
  let e := Cech.SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso
    (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
      ((Scheme.Modules.pullback b).obj N))) (b ⁻¹ᵁ U) (a ⁻¹ᵁ V)
  let x := AmbientExternalSectionPairing.ambientExternalSectionTensorMap a b cX cY hc M N V U (n ⊗ₜ[R] m)
  change e.hom (e.inv x) = x
  exact ConcreteCategory.congr_hom e.inv_hom_id x

theorem nativeAmbientExternalSectionMap_parameter_restrict
    (V : X.Opens) {U U' : Y.Opens} (hU : U' ≤ U)
    (n : (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U))
    (m : (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj (op V)) :
    (Cech.SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction
      (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
        ((Scheme.Modules.pullback b).obj N)))
      (leOfHom ((Opens.map b.base).map (homOfLE hU)))).hom.app (op (a ⁻¹ᵁ V))
        ((nativeAmbientExternalSectionMap a b cX cY hc M N U).app (op V) (n ⊗ₜ[R] m)) =
      (nativeAmbientExternalSectionMap a b cX cY hc M N U').app (op V)
        ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).map (homOfLE hU).op n ⊗ₜ[R] m) := by
  let F : P.carrier.Sheaf AddCommGrpCat.{u} := UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
    ((Scheme.Modules.pullback b).obj N))
  let e := Cech.SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso F (b ⁻¹ᵁ U') (a ⁻¹ᵁ V)
  have hi : Function.Injective e.hom :=
    (AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance
  apply hi
  let hB : b ⁻¹ᵁ U' ≤ b ⁻¹ᵁ U := leOfHom ((Opens.map b.base).map (homOfLE hU))
  have hmap := Cech.SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction_sections_mapIso F hB (a ⁻¹ᵁ V)
    ((nativeAmbientExternalSectionMap a b cX cY hc M N U).app (op V) (n ⊗ₜ[R] m))
  have hleft := nativeAmbientExternalSectionMap_tmul a b cX cY hc M N V U n m
  have hright := nativeAmbientExternalSectionMap_tmul a b cX cY hc M N V U'
    ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).map (homOfLE hU).op n) m
  have h := AmbientExternalSectionPairing.ambientExternalSectionTensorMap_naturality a b cX cY hc M N
    (show V ≤ V from le_rfl) hU n m
  have hid : (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).map
      (homOfLE (show V ≤ V from le_rfl)).op m = m := by
    change (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).map (𝟙 (op V)) m = m
    exact ConcreteCategory.congr_hom ((Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).map_id (op V)) m
  rw [hid] at h
  exact hmap.trans ((congrArg (F.obj.map (homOfLE (inf_le_inf_left (a ⁻¹ᵁ V) hB)).op) hleft).trans
    (h.symm.trans hright.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientExternalPresheafMap
