import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Basis Action Relations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.BasisActionRelations

noncomputable section

/-! A ring action is determined by its values on an integral basis.
The unit and basis-product equations suffice, even for noncommutative endomorphism rings. -/

open _root_.Module

variable {R A I : Type*} [Ring R] [Ring A] (b : Basis I ℤ R) (v : I → A)

def IntegralBasisActionRelations : Prop :=
  b.constr ℤ v 1 = 1 ∧ ∀ i j, b.constr ℤ v (b i * b j) = v i * v j

theorem integralBasisAction_map_mul (h : IntegralBasisActionRelations b v) :
    ∀ x y, b.constr ℤ v (x * y) = b.constr ℤ v x * b.constr ℤ v y := by
  apply (LinearMap.map_mul_iff (b.constr ℤ v)).mpr
  apply LinearMap.ext_basis b b
  intro i j
  change b.constr ℤ v (b i * b j) = b.constr ℤ v (b i) * b.constr ℤ v (b j)
  rw [Basis.constr_basis, Basis.constr_basis]
  exact h.2 i j

def ringHomOfIntegralBasis (h : IntegralBasisActionRelations b v) : R →+* A :=
  (AlgHom.ofLinearMap (b.constr ℤ v) h.1 (integralBasisAction_map_mul b v h)).toRingHom

theorem ringHomOfIntegralBasis_apply (h : IntegralBasisActionRelations b v) (i : I) :
    ringHomOfIntegralBasis b v h (b i) = v i := Basis.constr_basis b ℤ v i

theorem ringHom_ext_integralBasis {f g : R →+* A} (h : ∀ i, f (b i) = g (b i)) : f = g := by
  have he : f.toIntAlgHom.toLinearMap = g.toIntAlgHom.toLinearMap := b.ext h
  exact RingHom.ext (fun x => LinearMap.congr_fun he x)

theorem existsUnique_ringHom_of_integralBasis (h : IntegralBasisActionRelations b v) :
    ∃! f : R →+* A, ∀ i, f (b i) = v i := by
  refine ⟨ringHomOfIntegralBasis b v h, ringHomOfIntegralBasis_apply b v h, ?_⟩
  intro f hf
  exact ringHom_ext_integralBasis b (fun i => (hf i).trans (ringHomOfIntegralBasis_apply b v h i).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.BasisActionRelations
