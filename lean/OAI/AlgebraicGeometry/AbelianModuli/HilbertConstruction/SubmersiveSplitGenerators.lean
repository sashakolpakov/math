import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveSplitEvaluation
import Mathlib.RingTheory.Extension.Generators

/-! # Submersive Split Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveSplitGenerators

noncomputable section

/-! Selected variables generate an algebra over the polynomial algebra in the unselected variables. -/

universe u v w t

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {ι : Type w} {σ : Type t} (m : σ → ι) (v : ι → S)

abbrev submersiveFreeVariableAlgebra : Algebra (MvPolynomial (SubmersivePolynomialSplit.UnselectedVariables m) R) S :=
  (MvPolynomial.aeval (fun i : SubmersivePolynomialSplit.UnselectedVariables m => v i.val)).toAlgebra

theorem submersiveFreeVariableTower :
    letI := submersiveFreeVariableAlgebra R S m v
    IsScalarTower R (MvPolynomial (SubmersivePolynomialSplit.UnselectedVariables m) R) S := by
  let := submersiveFreeVariableAlgebra R S m v
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (MvPolynomial.aeval (fun i : SubmersivePolynomialSplit.UnselectedVariables m => v i.val)).commutes r |>.symm

theorem submersiveSplitEvaluation_eq_aeval :
    letI := submersiveFreeVariableAlgebra R S m v
    SubmersiveSplitEvaluation.submersiveSplitEvaluation R S m v = (MvPolynomial.aeval (fun j => v (m j))).toRingHom := rfl

def submersiveSplitGenerators (hm : Function.Injective m) (P : Algebra.Generators R S ι) :
    letI := submersiveFreeVariableAlgebra R S m P.val
    Algebra.Generators (MvPolynomial (SubmersivePolynomialSplit.UnselectedVariables m) R) S σ := by
  letI := submersiveFreeVariableAlgebra R S m P.val
  exact
    { val := fun j => P.val (m j)
      σ' := fun s => SubmersivePolynomialSplit.submersivePolynomialSplit R m hm (P.σ s)
      aeval_val_σ' := fun s =>
        (SubmersiveSplitEvaluation.submersiveSplitEvaluation_apply R S m hm P.val (P.σ s)).trans (P.aeval_val_σ s) }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveSplitGenerators
