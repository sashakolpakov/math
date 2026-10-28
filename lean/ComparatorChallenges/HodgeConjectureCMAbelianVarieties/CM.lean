module

public import HodgeConjecture.Variants
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Complex multiplication on geometric rational H¹

The Hodge filtration and cohomology are those of `HodgeConjecture`.
Each CM-field factor acts on its own rank-one summand of rational H¹.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint
open scoped TensorProduct

namespace HodgeCM

/-- Coordinatewise multiplication, transported to a rational vector space. -/
def diagonalAction {V : Type*} [AddCommGroup V] [Module ℚ V]
    {ι : Type*} (K : ι → Type) [∀ i, Field (K i)] [∀ i, Algebra ℚ (K i)]
    (e : V ≃ₗ[ℚ] ((i : ι) → K i)) (a : (i : ι) → K i) : Module.End ℚ V :=
  e.symm.toLinearMap ∘ₗ LinearMap.mul ℚ ((i : ι) → K i) a ∘ₗ e.toLinearMap

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The geometric rational-to-de Rham comparison extended to complex coefficients. -/
def h1Comparison : ℂ ⊗[ℚ] H^1(X; ℚ) →ₗ[ℚ] H_dR^1(X) :=
  TensorProduct.lift
    ((Algebra.lsmul ℚ ℚ H_dR^1(X)).toLinearMap.compl₂
      (fieldToDeRhamCohomologyLinear ℚ X 1))

/-- Complex multiplication means that rational H¹ is a finite direct sum of
rank-one spaces over CM number fields, whose diagonal action preserves the
geometric holomorphic Hodge filtration. The fields may differ between factors. -/
structure CMH1Data where
  factors : ℕ
  field : Fin factors → Type
  [fieldStructure : ∀ i, Field (field i)]
  [numberField : ∀ i, NumberField (field i)]
  [cmField : ∀ i, NumberField.IsCMField (field i)]
  model : H^1(X; ℚ) ≃ₗ[ℚ] ((i : Fin factors) → field i)
  preserves_hodgeFiltration : ∀ (a : (i : Fin factors) → field i)
      (z : ℂ ⊗[ℚ] H^1(X; ℚ)),
    h1Comparison X z ∈ hodgeFiltrationComplexSubmodule X 1 1 →
    h1Comparison X
        (TensorProduct.map LinearMap.id (diagonalAction field model a) z) ∈
      hodgeFiltrationComplexSubmodule X 1 1

attribute [instance] CMH1Data.fieldStructure CMH1Data.numberField CMH1Data.cmField

/-- The existence of geometric H¹ complex-multiplication data. -/
def HasComplexMultiplication : Prop := Nonempty (CMH1Data X)

end HodgeCM
