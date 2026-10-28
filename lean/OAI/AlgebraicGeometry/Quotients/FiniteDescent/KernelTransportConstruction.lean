import Mathlib.LinearAlgebra.Prod

/-! # Kernel Transport Construction -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.KernelTransportConstruction.Construction.KernelTransport

noncomputable section

/-! Transport of a kernel through an actual linear equivalence. -/

variable {R A B C : Type*} [CommRing R]
variable [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
variable [AddCommGroup C] [Module R C]

def equiv (e : A ≃ₗ[R] B) (f : A →ₗ[R] C) (g : B →ₗ[R] C)
    (h : g.comp e.toLinearMap = f) : f.ker ≃ₗ[R] g.ker where
  toFun x := ⟨e x.val, by
    change g (e x.val) = 0
    exact (LinearMap.congr_fun h x.val).trans x.property⟩
  invFun y := ⟨e.symm y.val, by
    change f (e.symm y.val) = 0
    rw [← h, LinearMap.comp_apply]
    change g (e (e.symm y.val)) = 0
    rw [e.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e.map_add _ _)
  map_smul' r x := Subtype.ext (e.map_smul _ _)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.KernelTransportConstruction.Construction.KernelTransport
