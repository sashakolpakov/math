import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Unary Tensor Power -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.UnaryTensorPower

noncomputable section

/-! A normalized degree-one tensor-power isomorphism sends the actual
first power of a section back to that section. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}}

def canonicalUnaryTensorPowerHom (M : X.Modules) : TensorPower.PowerSheaf.tensorPowerModule M 1 ⟶ M :=
  (TensorPower.PowerSheaf.tensorPowerHomEquiv M M 1).symm (Tensor.Powers.SheafMultilinearMap.unary M)

theorem canonicalUnaryTensorPowerHom_spec (M : X.Modules) :
    (TensorPower.Maps.tensorPowerMultilinear M 1).postcomp (canonicalUnaryTensorPowerHom M) =
      Tensor.Powers.SheafMultilinearMap.unary M :=
  (TensorPower.Maps.tensorPowerMultilinear_postcomp _).trans ((TensorPower.PowerSheaf.tensorPowerHomEquiv M M 1).apply_symm_apply _)

def canonicalUnaryTensorPowerIso (M : X.Modules) : TensorPower.PowerSheaf.tensorPowerModule M 1 ≅ M where
  hom := canonicalUnaryTensorPowerHom M
  inv := (TensorPower.Maps.tensorPowerMultilinear M 1).unaryToHom
  hom_inv_id := by
    apply TensorPower.Maps.tensorPower_hom_ext
    rw [Tensor.Powers.SheafMultilinearMap.postcomp_comp, canonicalUnaryTensorPowerHom_spec,
      Tensor.Powers.SheafMultilinearMap.unary_postcomp_unaryToHom, Tensor.Powers.SheafMultilinearMap.postcomp_id]
  inv_hom_id := by
    have h := congrArg Tensor.Powers.SheafMultilinearMap.unaryToHom (canonicalUnaryTensorPowerHom_spec M)
    have hn : ((TensorPower.Maps.tensorPowerMultilinear M 1).postcomp (canonicalUnaryTensorPowerHom M)).unaryToHom =
        (TensorPower.Maps.tensorPowerMultilinear M 1).unaryToHom ≫ canonicalUnaryTensorPowerHom M := by
      apply Scheme.Modules.hom_ext
      intro U
      apply ConcreteCategory.hom_ext
      intro r
      rfl
    rw [hn] at h
    exact h.trans (by
      simpa only [Tensor.Powers.SheafMultilinearMap.postcomp_id] using
        (Tensor.Powers.SheafMultilinearMap.unaryToHom_unary_postcomp (𝟙 M)))

theorem canonicalUnaryTensorPowerIso_section (M : X.Modules) (s : Line.Bundles.structureModule X ⟶ M) :
    TensorPower.Maps.tensorPowerSection s 1 ≫ (canonicalUnaryTensorPowerIso M).hom = s := by
  apply (Global.Sections.moduleSectionHomEquiv M).injective
  change (canonicalUnaryTensorPowerHom M).app ⊤
    ((TensorPower.Maps.tensorPowerSection s 1).app ⊤ (1 : Γ(X, ⊤))) = s.app ⊤ (1 : Γ(X, ⊤))
  rw [TensorPower.Maps.tensorPowerSection_app, one_smul]
  exact congrArg (fun β : Tensor.Powers.SheafMultilinearMap M 1 M =>
    β.app ⊤ (fun _ => s.app ⊤ (1 : Γ(X, ⊤)))) (canonicalUnaryTensorPowerHom_spec M)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.UnaryTensorPower
