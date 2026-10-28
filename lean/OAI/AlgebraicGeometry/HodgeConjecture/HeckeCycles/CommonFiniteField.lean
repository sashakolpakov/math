import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maximal

/-! # Common Finite Field -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonFiniteField.CM

noncomputable section

/-! Two finite evaluation fields admit a common finite extension.
A maximal-ideal quotient of their tensor product constructs the field
and both embeddings over the original coefficient field. -/

open scoped TensorProduct

variable (K L₁ L₂ : Type) [Field K] [Field L₁] [Field L₂]
  [Algebra K L₁] [Algebra K L₂] [Module.Finite K L₁] [Module.Finite K L₂]

structure CommonField where
  carrier : Type
  [field : Field carrier]
  [algebra : Algebra K carrier]
  [finite : Module.Finite K carrier]
  left : L₁ →ₐ[K] carrier
  right : L₂ →ₐ[K] carrier

attribute [instance] CommonField.field CommonField.algebra CommonField.finite

def commonField : CommonField K L₁ L₂ := Classical.choice (show Nonempty (CommonField K L₁ L₂) from by
  let A := L₁ ⊗[K] L₂
  let : Nontrivial A := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
    K L₁ L₂ (algebraMap K L₁).injective (algebraMap K L₂).injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  exact ⟨{
    carrier := A ⧸ m
    left := (Ideal.Quotient.mkₐ K m).comp Algebra.TensorProduct.includeLeft
    right := (Ideal.Quotient.mkₐ K m).comp Algebra.TensorProduct.includeRight }⟩)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonFiniteField.CM
