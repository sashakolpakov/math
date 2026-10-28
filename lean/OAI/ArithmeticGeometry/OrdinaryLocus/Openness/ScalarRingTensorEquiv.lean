import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CochainBaseChangeCycles

/-! # Scalar Ring Tensor Equiv -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ScalarRingTensorEquiv.Construction

noncomputable section

/-! Canonical tensor comparison when the coefficient rings are isomorphic over the base. -/

open _root_.CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable (r : R →+* A) (s : R →+* B) (e : A ≃+* B) (h : ∀ x, e (r x) = s x)

def scalarRingLinearEquiv :
    (ModuleCat.restrictScalars r).obj (ModuleCat.of A A) ≃ₗ[R]
      (ModuleCat.restrictScalars s).obj (ModuleCat.of B B) :=
  { e.toAddEquiv with
    map_smul' := by
      intro x a
      let a' : A := a
      change e (r x * a') = s x * e a'
      rw [e.map_mul, h] }

def scalarRingTensorAddEquiv (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars r).obj M ≃+ (ModuleCat.extendScalars s).obj M :=
  ((scalarRingLinearEquiv r s e h).rTensor M).toAddEquiv

theorem scalarRingTensorAddEquiv_tmul (M : ModuleCat.{u} R) (a : A) (m : M) :
    scalarRingTensorAddEquiv r s e h M (a ⊗ₜ[R,r] m) = e a ⊗ₜ[R,s] m :=
  rfl

theorem scalarRingTensorAddEquiv_naturality {M N : ModuleCat.{u} R} (q : M ⟶ N)
    (z : (ModuleCat.extendScalars r).obj M) :
    scalarRingTensorAddEquiv r s e h N ((ModuleCat.extendScalars r).map q z) =
      (ModuleCat.extendScalars s).map q (scalarRingTensorAddEquiv r s e h M z) := by
  let f := (scalarRingTensorAddEquiv r s e h N).toAddMonoidHom.comp
    ((ModuleCat.extendScalars r).map q).hom.toAddMonoidHom
  let g := ((ModuleCat.extendScalars s).map q).hom.toAddMonoidHom.comp
    (scalarRingTensorAddEquiv r s e h M).toAddMonoidHom
  change f z = g z
  induction z using TensorProduct.inductionOn with
  | tmul a m => rfl
  | add x y hx hy =>
      exact (map_add f x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add g x y).symm)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ScalarRingTensorEquiv.Construction
