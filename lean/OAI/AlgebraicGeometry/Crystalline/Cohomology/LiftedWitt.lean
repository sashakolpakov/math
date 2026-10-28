import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Comparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.FlatScalarExtension
import OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtension

/-! # Lifted Witt -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedWitt.LiftedWittScalarExtension

noncomputable section

/-! # Scalar extension commutes with the prescribed crystalline coefficient lifts -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k

def integral : ModuleCat.{u} W ⥤ ModuleCat.{u + 2} W :=
  PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift p k ⋙
    Affine.Comparison.AffineCrystallineComparison.largeLift p k ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : R ≃+* W).symm.toRingHom

def integralEquiv (M : ModuleCat.{u} W) : (integral p k).obj M ≃ₗ[W] M where
  toFun x := x.down.down
  invFun x := ULift.up (ULift.up x)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (S : Type u) [CommRing S] [Algebra (WittVector p k) S]

def source : ModuleCat.{u} W ⥤ ModuleCat.{u + 2} S :=
  integral p k ⋙ Large.FlatScalarExtension.LargeFlatScalarExtension.functor W S

def target : ModuleCat.{u} W ⥤ ModuleCat.{u + 2} S :=
  IntrinsicScalarExtension.functor W S ⋙ ModuleCat.uliftFunctor.{u + 2} S

instance source_additive : (source p k S).Additive := by
  unfold source integral
  infer_instance

instance target_additive : (target p k S).Additive := by
  unfold target
  infer_instance

def componentEquiv (M : ModuleCat.{u} W) : (source p k S).obj M ≃ₗ[S] (target p k S).obj M :=
  ((integralEquiv p k M).baseChange W S _ _).trans ULift.moduleEquiv.symm

theorem componentEquiv_tmul (M : ModuleCat.{u} W) (a : S) (x : (integral p k).obj M) :
    componentEquiv p k S M (a ⊗ₜ[W] x) = ULift.up (a ⊗ₜ[W] x.down.down) := rfl

def iso : source p k S ≅ target p k S :=
  NatIso.ofComponents (fun M => (componentEquiv p k S M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    let g : (source p k S).obj M →ₗ[S] (target p k S).obj N :=
      (componentEquiv p k S N).toLinearMap.comp ((source p k S).map f).hom
    let h : (source p k S).obj M →ₗ[S] (target p k S).obj N :=
      ((target p k S).map f).hom.comp (componentEquiv p k S M).toLinearMap
    change g z = h z
    induction z using TensorProduct.inductionOn with
    | tmul a x => rfl
    | add x y hx hy =>
      exact (map_add g x y).trans
        ((congrArg₂ (fun a b => a + b) hx hy).trans (map_add h x y).symm))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedWitt.LiftedWittScalarExtension
