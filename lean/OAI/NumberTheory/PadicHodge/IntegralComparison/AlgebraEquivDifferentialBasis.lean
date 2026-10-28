import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Algebra Equiv Differential Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraEquivDifferentialBasis

noncomputable section

/-! A differential basis transports through an actual algebra
isomorphism, with the differentials of the literal transported parameters. -/
open scoped TensorProduct
universe u v w t
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A]
  {B : Type w} [CommRing B] [Algebra R A] [Algebra R B]
  (e : A ≃ₐ[R] B)

@[instance_reducible]
def scalarAlgebra : Algebra A B := e.toRingHom.toAlgebra

theorem scalarTower : letI := scalarAlgebra e; IsScalarTower R A B := by
  let := scalarAlgebra e
  exact IsScalarTower.of_algebraMap_eq (fun r => (e.commutes r).symm)

theorem formallyEtale : letI := scalarAlgebra e; Algebra.FormallyEtale A B := by
  let := scalarAlgebra e
  let e' : A ≃ₐ[A] B := { e.toRingEquiv with commutes' := fun _ => rfl }
  exact Algebra.FormallyEtale.of_equiv e'

variable {ι : Type t} (b : Module.Basis ι A Ω[A⁄R])

def basis : Module.Basis ι B Ω[B⁄R] := by
  letI := scalarAlgebra e
  letI := scalarTower e
  letI := formallyEtale e
  exact (b.baseChange B).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B)

theorem basis_apply (x : ι → A) (hx : ∀ i, b i = KaehlerDifferential.D R A (x i)) (i : ι) :
    basis e b i = KaehlerDifferential.D R B (e (x i)) := by
  let := scalarAlgebra e
  let := scalarTower e
  let := formallyEtale e
  rw [basis, Module.Basis.map_apply, Module.Basis.baseChange_apply, hx]
  change KaehlerDifferential.mapBaseChange R A B ((1 : B) ⊗ₜ[A] KaehlerDifferential.D R A (x i)) = _
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraEquivDifferentialBasis
