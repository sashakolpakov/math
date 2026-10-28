import OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChange

/-! # Module Base Change Functor -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeFunctor

noncomputable section

/-!
# Functorial affine module base change for PoincareBundle
-/

open _root_.CategoryTheory TensorProduct
open scoped TensorProduct
open scoped ChangeOfRings

universe u

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Restriction from S followed by extension to T. -/
def sourceFunctor : ModuleCat.{u} S ⥤ ModuleCat.{u} T :=
  ModuleCat.restrictScalars (algebraMap R S) ⋙ ModuleCat.extendScalars (algebraMap R T)

/-- Extension to the tensor ring followed by restriction to T. -/
def targetFunctor : ModuleCat.{u} S ⥤ ModuleCat.{u} T :=
  ModuleCat.extendScalars (algebraMap S (S ⊗[R] T)) ⋙
    ModuleCat.restrictScalars (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom

instance restrictedScalarTower (M : ModuleCat.{u} S) :
    IsScalarTower R S ((ModuleCat.restrictScalars (algebraMap R S)).obj M) := by
  constructor
  intro r s m
  change (r • s) • m = (algebraMap R S r) • (s • m)
  rw [Algebra.smul_def, mul_smul]

/-- The library's extension-of-scalars object agrees with the ordinary tensor model. -/
def sourceModelIso (M : ModuleCat.{u} S) :
    (sourceFunctor R S T).obj M ≅
      ModuleCat.of T (T ⊗[R] (ModuleCat.restrictScalars (algebraMap R S)).obj M) := by
  let T₀ := (ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T T)
  let e : T₀ ≃ₗ[T] T := LinearEquiv.refl T T
  exact (AlgebraTensorModule.congr e (LinearEquiv.refl R _)).toModuleIso

/-- The library's tensor-ring extension agrees with the ordinary tensor model. -/
def targetModelEquiv (M : ModuleCat.{u} S) :
    (targetFunctor R S T).obj M ≃ₗ[T] (S ⊗[R] T) ⊗[S] M := by
  let U₀ := (ModuleCat.restrictScalars (algebraMap S (S ⊗[R] T))).obj (ModuleCat.of (S ⊗[R] T) (S ⊗[R] T))
  let e : U₀ ≃ₗ[S] (S ⊗[R] T) := {
    toFun := id
    invFun := id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun s u => by
      change (algebraMap S (S ⊗[R] T) s) * (show (S ⊗[R] T) from u) = s • (show (S ⊗[R] T) from u)
      exact (Algebra.smul_def s (show (S ⊗[R] T) from u)).symm }
  let d := TensorProduct.congr e (LinearEquiv.refl S M)
  refine { __ := d.toAddEquiv, map_smul' := ?_ }
  intro t z
  change d ((Algebra.TensorProduct.includeRight : T →ₐ[R] (S ⊗[R] T)) t •
    (show U₀ ⊗[S] M from z)) = t • d z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => erw [smul_add, d.map_add, hx, hy, d.map_add, smul_add]
  | tmul u m =>
      change d ((show U₀ from
        (Algebra.TensorProduct.includeRight : T →ₐ[R] (S ⊗[R] T)) t * (show (S ⊗[R] T) from u)) ⊗ₜ[S] m) = _
      simp only [d, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
      rw [smul_tmul', Algebra.smul_def]
      rfl

/-- The objectwise affine base-change isomorphism between actual module functors. -/
def objectIso (M : ModuleCat.{u} S) :
    (sourceFunctor R S T).obj M ≅ (targetFunctor R S T).obj M := by
  let M₀ := (ModuleCat.restrictScalars (algebraMap R S)).obj M
  exact sourceModelIso R S T M ≪≫
    (ModuleBaseChange.baseChangeEquiv R S T M₀).symm.toModuleIso ≪≫
      (targetModelEquiv R S T M).symm.toModuleIso

/-- The forward base-change map includes the T-scalar in the second tensor factor. -/
theorem objectIso_hom_tmul (M : ModuleCat.{u} S) (t : T)
    (m : (ModuleCat.restrictScalars (algebraMap R S)).obj M) :
    (objectIso R S T M).hom (t ⊗ₜ[R,algebraMap R T] m) =
      (1 ⊗ₜ[R] t) ⊗ₜ[S,algebraMap S (S ⊗[R] T)] (show M from m) := by
  apply (targetModelEquiv R S T M).injective
  change targetModelEquiv R S T M ((targetModelEquiv R S T M).symm
    ((ModuleBaseChange.baseChangeEquiv R S T
      ((ModuleCat.restrictScalars (algebraMap R S)).obj M)).symm (t ⊗ₜ[R] m))) = _
  erw [LinearEquiv.apply_symm_apply]

/-- Module morphisms commute with the affine base-change comparison. -/
theorem objectIso_naturality {M N : ModuleCat.{u} S} (a : M ⟶ N) :
    (sourceFunctor R S T).map a ≫ (objectIso R S T N).hom =
      (objectIso R S T M).hom ≫ (targetFunctor R S T).map a := by
  apply ModuleCat.ExtendScalars.hom_ext (f := algebraMap R T)
  intro m
  change (objectIso R S T N).hom
      ((ModuleCat.extendScalars (algebraMap R T)).map
        ((ModuleCat.restrictScalars (algebraMap R S)).map a) ((1 : T) ⊗ₜ[R,algebraMap R T] m)) =
    ((ModuleCat.extendScalars (algebraMap S (S ⊗[R] T))).map a)
      ((objectIso R S T M).hom ((1 : T) ⊗ₜ[R,algebraMap R T] m))
  erw [ModuleCat.ExtendScalars.map_tmul, objectIso_hom_tmul]

/-- The natural isomorphism for affine direct-image base change on modules. -/
def baseChangeIso : sourceFunctor R S T ≅ targetFunctor R S T :=
  NatIso.ofComponents (objectIso R S T) (fun a => objectIso_naturality R S T a)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeFunctor
