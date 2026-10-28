import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionTensorMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.UnitRight
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.ModuleTensorTarget
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.ModuleTensorComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorSectionValues

/-! # Section Structure Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionStructureParameter

noncomputable section

/-! With the structure module as parameter, the canonical external section pairing is the native scalar tensor comparison, after the explicit right-unit identification. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

def parameterStructureSectionsEquiv {S Y : Scheme.{u}} (g : Y ⟶ S) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom (Line.Bundles.structureModule Y)).obj (op ⊤) ≃ₗ[Γ(S, ⊤)]
      Affine.TensorSectionComparison.morphismGlobalAlgebra g where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change Γ(Y, ⊤) at x
    change Y.presheaf.map (𝟙 (op (⊤ : Y.Opens))) (g.appTop r) * x = g.appTop r * x
    simp only [Y.presheaf.map_id, CommRingCat.id_apply]

def externalStructureParameterIso {Y P : Scheme.{u}} (b : P ⟶ Y) (M : P.Modules) :
    Tensor.ProductSheaf.tensorModule M ((Scheme.Modules.pullback b).obj (Line.Bundles.structureModule Y)) ≅ M :=
  Tensor.Bifunctor.tensorModuleMapIso (Iso.refl M) (Line.Bundles.structureModulePullbackIso b) ≪≫ Tensor.UnitRight.tensorModuleUnitRightIso M

def externalStructureParameterSectionsIso
    {R : Type u} [CommRing R] {X Y P : Scheme.{u}}
    (a : P ⟶ X) (b : P ⟶ Y) (cX : R →+* Γ(X, ⊤)) (M : X.Modules) (V : X.Opens) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf cX ((Scheme.Modules.pushforward a).obj
      (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
        ((Scheme.Modules.pullback b).obj (Line.Bundles.structureModule Y))))).obj (op V) ≅
    (Coefficient.ModulePresheaf.coefficientModulePresheaf cX ((Scheme.Modules.pushforward a).obj
      ((Scheme.Modules.pullback a).obj M))).obj (op V) :=
  ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor cX).mapIso ((Scheme.Modules.pushforward a).mapIso
    (externalStructureParameterIso b ((Scheme.Modules.pullback a).obj M)))).app (op V)

variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g) (M : X.Modules)

theorem externalSectionTensorMap_structure_tmul (V : X.Opens)
    (n : (Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom (Line.Bundles.structureModule Y)).obj (op ⊤))
    (m : (Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).obj (op V)) :
    (externalStructureParameterIso b ((Scheme.Modules.pullback a).obj M)).hom.app (a ⁻¹ᵁ V)
      (SectionTensorMap.externalSectionTensorMap a b f.appTop.hom g.appTop.hom
        (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M (Line.Bundles.structureModule Y) V (n ⊗ₜ[Γ(S, ⊤)] m)) =
    Module.SectionTensorComparison.moduleSectionTensorComparisonApp (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g) a f.appTop.hom M b.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) V
        (parameterStructureSectionsEquiv g n ⊗ₜ[Γ(S, ⊤)] m) := by
  let W := a ⁻¹ᵁ V
  let Ma := (Scheme.Modules.pullback a).obj M
  let Nb := (Scheme.Modules.pullback b).obj (Line.Bundles.structureModule Y)
  let u : Γ(Ma, W) := ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app V m
  let v : Γ(Nb, ⊤) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (Line.Bundles.structureModule Y)).app ⊤ n
  have hu : (Line.Bundles.structureModulePullbackIso b).hom.app ⊤ v = b.appTop n :=
    Structure.ModuleTensorTarget.baseChangedStructureModuleSectionsIso_unit b g.appTop.hom ⊤ n
  have hr : (Line.Bundles.structureModulePullbackIso b).hom.app W (Nb.presheaf.map W.leTop.op v) =
      P.presheaf.map W.leTop.op ((Line.Bundles.structureModulePullbackIso b).hom.app ⊤ v) :=
    ConcreteCategory.congr_hom ((Line.Bundles.structureModulePullbackIso b).hom.mapPresheaf.naturality W.leTop.op) v
  have hb := hr.trans (congrArg (P.presheaf.map W.leTop.op) hu)
  have ht := congrArg
    (fun β : Bilinear.Sheaves.SheafBilinearMap Ma Nb (Tensor.ProductSheaf.tensorModule Ma (Line.Bundles.structureModule P)) =>
      β.app W u (Nb.presheaf.map W.leTop.op v))
    (Tensor.Bifunctor.tensorModuleMap_spec (𝟙 Ma) (Line.Bundles.structureModulePullbackIso b).hom)
  change (Tensor.Bifunctor.tensorModuleMap (𝟙 Ma) (Line.Bundles.structureModulePullbackIso b).hom).app W
      ((Tensor.Bifunctor.tensorBilinear Ma Nb).app W u (Nb.presheaf.map W.leTop.op v)) =
    (Tensor.Bifunctor.tensorBilinear Ma (Line.Bundles.structureModule P)).app W u
      ((Line.Bundles.structureModulePullbackIso b).hom.app W (Nb.presheaf.map W.leTop.op v)) at ht
  have hp : (externalStructureParameterIso b Ma).hom.app W
      ((Tensor.Bifunctor.tensorBilinear Ma Nb).app W u (Nb.presheaf.map W.leTop.op v)) =
      P.presheaf.map W.leTop.op (b.appTop n) • u :=
    (congrArg ((Tensor.UnitRight.tensorModuleUnitRightIso Ma).hom.app W) ht).trans
      ((Tensor.UnitRight.tensorModuleUnitRightIso_pairing Ma W u
        ((Line.Bundles.structureModulePullbackIso b).hom.app W (Nb.presheaf.map W.leTop.op v))).trans
          (congrArg (fun z : Γ(P, W) => z • u) hb))
  have he := SectionTensorMap.externalSectionTensorMap_tmul a b f.appTop.hom g.appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M (Line.Bundles.structureModule Y) V n m
  exact ((congrArg ((externalStructureParameterIso b Ma).hom.app W) he).trans hp).trans
    (Module.TensorSectionValues.moduleSectionTensorComparisonApp_value (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
    a f.appTop.hom M b.appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) V
      (parameterStructureSectionsEquiv g n) m).symm

theorem externalSectionTensorMap_structure_comparison (V : X.Opens) :
    ModuleCat.ofHom (SectionTensorMap.externalSectionTensorMap a b f.appTop.hom g.appTop.hom
        (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M (Line.Bundles.structureModule Y) V) ≫
      (externalStructureParameterSectionsIso a b f.appTop.hom M V).hom =
    ModuleCat.ofHom ((parameterStructureSectionsEquiv g).toLinearMap.rTensor
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).obj (op V))) ≫
      ModuleCat.ofHom (Module.SectionTensorComparison.moduleSectionTensorComparisonApp (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
        a f.appTop.hom M b.appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) V) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro n m
  exact externalSectionTensorMap_structure_tmul H M V n m

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionStructureParameter
