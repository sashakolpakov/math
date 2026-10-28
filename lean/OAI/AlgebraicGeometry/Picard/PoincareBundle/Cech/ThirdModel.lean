import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing

/-! # Third Model -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ThirdModel

noncomputable section

/-!
# The third-coordinate pullback in the triple tensor model
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleExtension OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeFunctor

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{u} S)

local notation "U" => S ⊗[R] S

/-- Move the third coordinate to the first tensor position in the coefficient ring. -/
def thirdCoefficientTransport : TripleGluing.slotModule R S M (TripleGluing.slot3 R S) ≃+
    (extendScalars (algebraMap S (S ⊗[R] U))).obj M :=
  ExtensionTwist.extensionEquiv (TripleGluing.slot3 R S) (algebraMap S (S ⊗[R] U))
    (Algebra.TensorProduct.comm R U S).toRingEquiv (fun _ => rfl) M

/-- The third-coordinate module with the two remaining coordinates in reverse order. -/
def thirdFlatModel : TripleGluing.slotModule R S M (TripleGluing.slot3 R S) ≃+ TripleExtension.tripleModule R S M := by
  let e := thirdCoefficientTransport R S M
  let a := ModuleBaseChangeFunctor.targetModelEquiv R S U M
  let d := (ModuleBaseChange.baseChangeEquivR R S U
    ((restrictScalars (algebraMap R S)).obj M)).trans
      ((TensorProduct.assoc R S S ((restrictScalars (algebraMap R S)).obj M)).trans
        (TensorProduct.leftComm R S S ((restrictScalars (algebraMap R S)).obj M)))
  exact {
    toFun := fun z => d (a (e z))
    invFun := fun z => e.symm (a.symm (d.symm z))
    left_inv := fun z =>
      (congrArg (fun x => e.symm (a.symm x)) (d.symm_apply_apply (a (e z)))).trans
        ((congrArg e.symm (a.symm_apply_apply (e z))).trans (e.symm_apply_apply z))
    right_inv := fun z =>
      (congrArg (fun x => d (a x)) (e.apply_symm_apply (a.symm (d.symm z)))).trans
        ((congrArg d (a.apply_symm_apply (d.symm z))).trans (d.apply_symm_apply z))
    map_add' := fun x y =>
      (congrArg (fun z => d (a z)) (e.map_add x y)).trans
        ((congrArg d (a.map_add (e x) (e y))).trans (d.map_add (a (e x)) (a (e y)))) }

@[simp]
theorem thirdFlatModel_tmul (a b c : S) (m : M) :
    thirdFlatModel R S M (((a ⊗ₜ[R] b) ⊗ₜ[R] c) ⊗ₜ[S,TripleGluing.slot3 R S] m) =
      b ⊗ₜ[R] (a ⊗ₜ[R] (c •
        (show (restrictScalars (algebraMap R S)).obj M from m))) := by
  change TensorProduct.leftComm R S S ((restrictScalars (algebraMap R S)).obj M)
    (TensorProduct.assoc R S S ((restrictScalars (algebraMap R S)).obj M)
      (ModuleBaseChange.baseChangeEquivR R S U
        ((restrictScalars (algebraMap R S)).obj M)
          ((c ⊗ₜ[R] (a ⊗ₜ[R] b)) ⊗ₜ[S] m))) = _
  exact congrArg (fun z =>
    TensorProduct.leftComm R S S ((restrictScalars (algebraMap R S)).obj M)
      (TensorProduct.assoc R S S ((restrictScalars (algebraMap R S)).obj M) z))
    (ModuleBaseChange.baseChangeEquivR_tmul R S U
      ((restrictScalars (algebraMap R S)).obj M) c (a ⊗ₜ[R] b)
      (show (restrictScalars (algebraMap R S)).obj M from m))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ThirdModel
