import OAI.NumberTheory.PadicHodge.GeometricComparison.HomologyScalarExtension

/-! # Extension Tensor Equivalence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ExtensionTensorEquivalence.ChainScalarExtension

noncomputable section

/-! Identify the coefficient-extension functor's tensor product with the native tensor product of an algebra. -/

open _root_.CategoryTheory
open scoped TensorProduct ChangeOfRings

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

theorem coefficient_smul (r : R) (s : S) :
    @SMul.smul R S (Module.compHom S (algebraMap R S)).toSMul r s = r • s := by
  change algebraMap R S r • s = r • s
  exact IsScalarTower.algebraMap_smul S r s

def coefficientEquiv :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r s := coefficient_smul (R := R) (S := S) r s

def tensorObjEquiv (M : ModuleCat.{0} R) :
    (HomologyScalarExtension.ChainScalarExtension.extension (algebraMap R S)).obj M ≃ₗ[S] (S ⊗[R] M) := by
  letI : Module S ((HomologyScalarExtension.ChainScalarExtension.extension (algebraMap R S)).obj M) :=
    ((HomologyScalarExtension.ChainScalarExtension.extension (algebraMap R S)).obj M).isModule
  let e : (HomologyScalarExtension.ChainScalarExtension.extension (algebraMap R S)).obj M ≃+ (S ⊗[R] M) :=
    (TensorProduct.congr (coefficientEquiv (R := R) (S := S)) (LinearEquiv.refl R M)).toAddEquiv
  refine { e with map_smul' := ?_ }
  intro s x
  change e (s • x) = s • e x
  induction x using TensorProduct.inductionOn with
  | tmul a m => rfl
  | add x y hx hy =>
      erw [smul_add, e.map_add, hx, hy, e.map_add, smul_add]

theorem tensorObjEquiv_tmul (M : ModuleCat.{0} R) (s : S) (m : M) :
    tensorObjEquiv M (s ⊗ₜ[R, algebraMap R S] m) = s ⊗ₜ[R] m := rfl

theorem tensorObjEquiv_naturality {M N : ModuleCat.{0} R} (f : M ⟶ N)
    (x : (HomologyScalarExtension.ChainScalarExtension.extension (algebraMap R S)).obj M) :
    tensorObjEquiv N ((HomologyScalarExtension.ChainScalarExtension.extension (algebraMap R S)).map f x) =
      f.hom.baseChange S (tensorObjEquiv M x) := by
  let a : (HomologyScalarExtension.ChainScalarExtension.extension (algebraMap R S)).obj M ⟶ ModuleCat.of S (S ⊗[R] N) :=
    (HomologyScalarExtension.ChainScalarExtension.extension (algebraMap R S)).map f ≫ (tensorObjEquiv N).toModuleIso.hom
  let b : (HomologyScalarExtension.ChainScalarExtension.extension (algebraMap R S)).obj M ⟶ ModuleCat.of S (S ⊗[R] N) :=
    (tensorObjEquiv M).toModuleIso.hom ≫ ModuleCat.ofHom (f.hom.baseChange S)
  have he : a = b := ModuleCat.ExtendScalars.hom_ext (fun _ => rfl)
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom he) x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ExtensionTensorEquivalence.ChainScalarExtension
