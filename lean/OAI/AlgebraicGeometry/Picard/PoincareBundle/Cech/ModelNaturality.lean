import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels

/-! # Model Naturality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModelNaturality

noncomputable section

/-!
# Naturality of the two actual affine Čech tensor models
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels

/-- Additivity in the actual coefficient module used by scalar extension. -/
theorem extension_add_tmul {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (M : ModuleCat.{u} A) (x y : B) (m : M) :
    (show (extendScalars f).obj M from (x + y) ⊗ₜ[A,f] m) =
      x ⊗ₜ[A,f] m + y ⊗ₜ[A,f] m :=
  TensorProduct.add_tmul (R := A) (M := (restrictScalars f).obj (ModuleCat.of B B)) x y m

/-- The coefficient variable of a scalar extension, followed by any additive model. -/
def coefficientMap {A B P : Type u} [CommRing A] [CommRing B] [AddCommGroup P]
    (f : A →+* B) (M : ModuleCat.{u} A) (e : (extendScalars f).obj M →+ P) (m : M) : B →+ P where
  toFun x := e (x ⊗ₜ[A,f] m)
  map_zero' := (congrArg e (TensorProduct.zero_tmul (R := A)
    ((restrictScalars f).obj (ModuleCat.of B B)) m)).trans e.map_zero
  map_add' x y := (congrArg e (extension_add_tmul f M x y m)).trans (e.map_add _ _)

/-- Naturality of additive models can be checked on the actual scalar-extension generators. -/
theorem extension_model_naturality {A B P Q : Type u} [CommRing A] [CommRing B]
    [AddCommGroup P] [AddCommGroup Q] (f : A →+* B) {M N : ModuleCat.{u} A} (a : M ⟶ N)
    (eM : (extendScalars f).obj M →+ P) (eN : (extendScalars f).obj N →+ Q) (t : P →+ Q)
    (h : ∀ x m, eN (x ⊗ₜ[A,f] a m) = t (eM (x ⊗ₜ[A,f] m)))
    (z : (extendScalars f).obj M) : eN ((extendScalars f).map a z) = t (eM z) := by
  let b := eN.comp ((extendScalars f).map a).hom.toAddMonoidHom
  let c := t.comp eM
  change b z = c z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      exact (b.map_add x y).trans ((congrArg₂ (fun s t => s + t) hx hy).trans (c.map_add x y).symm)
  | tmul x m => exact (congrArg eN (ExtendScalars.map_tmul f a x m)).trans (h x m)

/-- An additive map out of the coefficient tensor ring is determined on pure tensors. -/
theorem coefficient_ext {R S P : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup P] (b c : S ⊗[R] S →+ P)
    (h : ∀ s t, b (s ⊗ₜ[R] t) = c (s ⊗ₜ[R] t)) (x : S ⊗[R] S) : b x = c x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      exact (b.map_add x y).trans ((congrArg₂ (fun s t => s + t) hx hy).trans (c.map_add x y).symm)
  | tmul s t => exact h s t

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  {M N : ModuleCat.{u} S} (a : M ⟶ N)

/-- The original-module map on the coefficient/module tensor model. -/
def tensorMap : S ⊗[R] (restrictScalars (algebraMap R S)).obj M →ₗ[R]
    S ⊗[R] (restrictScalars (algebraMap R S)).obj N :=
  TensorProduct.map (LinearMap.id : S →ₗ[R] S) ((restrictScalars (algebraMap R S)).map a).hom

/-- The first affine pullback model is natural for every original-module morphism. -/
theorem firstModel_naturality (z : ModuleModels.firstPullback R S M) :
    ModuleModels.firstModel R S N ((extendScalars (ModuleModels.firstMap R S)).map a z) =
      tensorMap R S a (ModuleModels.firstModel R S M z) := by
  apply extension_model_naturality (ModuleModels.firstMap R S) a (ModuleModels.firstModel R S M).toAddMonoidHom
    (ModuleModels.firstModel R S N).toAddMonoidHom (tensorMap R S a).toAddMonoidHom
  intro x m
  apply coefficient_ext
    (coefficientMap (ModuleModels.firstMap R S) N (ModuleModels.firstModel R S N).toAddMonoidHom (a m))
    ((tensorMap R S a).toAddMonoidHom.comp
      (coefficientMap (ModuleModels.firstMap R S) M (ModuleModels.firstModel R S M).toAddMonoidHom m)) _ x
  intro s t
  change ModuleModels.firstModel R S N ((s ⊗ₜ[R] t) ⊗ₜ[S,ModuleModels.firstMap R S] a m) =
    tensorMap R S a (ModuleModels.firstModel R S M ((s ⊗ₜ[R] t) ⊗ₜ[S,ModuleModels.firstMap R S] m))
  erw [ModuleModels.firstModel_tmul, ModuleModels.firstModel_tmul]
  exact congrArg (fun n : N => t ⊗ₜ[R]
    (show (restrictScalars (algebraMap R S)).obj N from n)) (a.hom.map_smul s m).symm

/-- The second affine pullback model is natural for every original-module morphism. -/
theorem secondModel_naturality (z : ModuleModels.secondPullback R S M) :
    ModuleModels.secondModel R S N ((extendScalars (ModuleModels.secondMap R S)).map a z) =
      tensorMap R S a (ModuleModels.secondModel R S M z) := by
  apply extension_model_naturality (ModuleModels.secondMap R S) a (ModuleModels.secondModel R S M).toAddMonoidHom
    (ModuleModels.secondModel R S N).toAddMonoidHom (tensorMap R S a).toAddMonoidHom
  intro x m
  apply coefficient_ext
    (coefficientMap (ModuleModels.secondMap R S) N (ModuleModels.secondModel R S N).toAddMonoidHom (a m))
    ((tensorMap R S a).toAddMonoidHom.comp
      (coefficientMap (ModuleModels.secondMap R S) M (ModuleModels.secondModel R S M).toAddMonoidHom m)) _ x
  intro s t
  change ModuleModels.secondModel R S N ((s ⊗ₜ[R] t) ⊗ₜ[S,ModuleModels.secondMap R S] a m) =
    tensorMap R S a (ModuleModels.secondModel R S M ((s ⊗ₜ[R] t) ⊗ₜ[S,ModuleModels.secondMap R S] m))
  erw [ModuleModels.secondModel_tmul, ModuleModels.secondModel_tmul]
  exact congrArg (fun n : N => s ⊗ₜ[R]
    (show (restrictScalars (algebraMap R S)).obj N from n)) (a.hom.map_smul t m).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModelNaturality
