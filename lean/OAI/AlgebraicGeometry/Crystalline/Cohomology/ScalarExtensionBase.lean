import OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtension
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.TensorMap

/-! # Scalar Extension Base -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ScalarExtensionBase.ScalarExtensionTwist

noncomputable section

/-! # Scalar extension commutes with compatible coefficient automorphisms -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (e : R ≃+* R) (t : S ≃+* S)
  (h : ∀ r, t (algebraMap R S r) = algebraMap R S (e r))

local notation "Q" => ModuleCat.restrictScalars e.toRingHom
local notation "T" => ModuleCat.restrictScalars t.toRingHom
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtension.functor R S

def tensor (M : ModuleCat.{u} R) (s : S) (x : M) : (P).obj M := s ⊗ₜ[R] x

include h in
theorem inverse_base (r : R) :
    t.symm (algebraMap R S r) = algebraMap R S (e.symm r) := by
  apply t.injective
  rw [t.apply_symm_apply, h, e.apply_symm_apply]

def untwist (M : ModuleCat.{u} R) : (Q).obj M →ₛₗ[e.toRingHom] M where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def retwist (M : ModuleCat.{u} R) : M →ₛₗ[e.symm.toRingHom] (Q).obj M where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' r x := by
    change r • x = e (e.symm r) • x
    rw [e.apply_symm_apply]

def forward (M : ModuleCat.{u} R) : (P).obj ((Q).obj M) ⟶ (T).obj ((P).obj M) :=
  ModuleCat.ofHom (X := (P).obj ((Q).obj M)) (Y := (T).obj ((P).obj M)) {
    toFun := Semilinear.TensorMap.SemilinearTensorMap.map e.toRingHom t.toRingHom h (untwist R e M)
    map_add' := map_add _
    map_smul' s z := (Semilinear.TensorMap.SemilinearTensorMap.map e.toRingHom t.toRingHom h (untwist R e M)).map_smulₛₗ s z }

def backward (M : ModuleCat.{u} R) : (P).obj M →ₛₗ[t.symm.toRingHom] (P).obj ((Q).obj M) :=
  Semilinear.TensorMap.SemilinearTensorMap.map e.symm.toRingHom t.symm.toRingHom (inverse_base R S e t h) (retwist R e M)

theorem forward_tmul (M : ModuleCat.{u} R) (s : S) (x : (Q).obj M) :
    (forward R S e t h M).hom (tensor R S ((Q).obj M) s x) = tensor R S M (t s) x := rfl

theorem backward_tmul (M : ModuleCat.{u} R) (s : S) (x : M) :
    backward R S e t h M (tensor R S M s x) = tensor R S ((Q).obj M) (t.symm s) x := rfl

theorem left_inverse (M : ModuleCat.{u} R) :
    Function.LeftInverse (backward R S e t h M) (forward R S e t h M) := by
  intro z
  change backward R S e t h M ((forward R S e t h M).hom z) = z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact (congrArg (backward R S e t h M) ((forward R S e t h M).hom.map_add x y)).trans
      (((backward R S e t h M).map_add _ _).trans (congrArg₂ (fun a b => a + b) hx hy))
  | tmul s x =>
    exact (congrArg (backward R S e t h M) (forward_tmul R S e t h M s x)).trans
      ((backward_tmul R S e t h M (t s) x).trans
        (congrArg (fun a => tensor R S ((Q).obj M) a x) (t.symm_apply_apply s)))

theorem right_inverse (M : ModuleCat.{u} R) :
    Function.RightInverse (backward R S e t h M) (forward R S e t h M) := by
  intro z
  change (forward R S e t h M).hom (backward R S e t h M z) = z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact (congrArg (forward R S e t h M).hom ((backward R S e t h M).map_add x y)).trans
      (((forward R S e t h M).hom.map_add _ _).trans (congrArg₂ (fun a b => a + b) hx hy))
  | tmul s x =>
    exact (congrArg (forward R S e t h M).hom (backward_tmul R S e t h M s x)).trans
      ((forward_tmul R S e t h M (t.symm s) x).trans
        (congrArg (fun a => tensor R S M a x) (t.apply_symm_apply s)))

def componentIso (M : ModuleCat.{u} R) : (P).obj ((Q).obj M) ≅ (T).obj ((P).obj M) :=
  (LinearEquiv.ofBijective (forward R S e t h M).hom
    ⟨(left_inverse R S e t h M).injective, (right_inverse R S e t h M).surjective⟩).toModuleIso

theorem naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (P).map ((Q).map f) ≫ (componentIso R S e t h N).hom =
      (componentIso R S e t h M).hom ≫ (T).map ((P).map f) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  let a := ((P).map ((Q).map f) ≫ (componentIso R S e t h N).hom).hom
  let b := ((componentIso R S e t h M).hom ≫ (T).map ((P).map f)).hom
  intro z
  change a z = b z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact (a.map_add x y).trans ((congrArg₂ (fun c d => c + d) hx hy).trans (b.map_add x y).symm)
  | tmul s x => rfl

def iso : Q ⋙ P ≅ P ⋙ T :=
  NatIso.ofComponents (componentIso R S e t h) (fun f => naturality R S e t h f)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ScalarExtensionBase.ScalarExtensionTwist
