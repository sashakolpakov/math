import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveSplitPresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveSplitDifferential
import Mathlib.RingTheory.Extension.Presentation.Submersive

/-! # Submersive Split Jacobian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveSplitJacobian

noncomputable section

/-! The selected-coordinate presentation has the same evaluated Jacobian. -/

universe u v w t

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {ι : Type w} {σ : Type t} (P : Algebra.PreSubmersivePresentation R S ι σ)

def submersiveSplitPrePresentation :
    letI := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S P.map P.val
    Algebra.PreSubmersivePresentation (MvPolynomial (SubmersivePolynomialSplit.UnselectedVariables P.map) R) S σ σ := by
  letI := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S P.map P.val
  exact
    { toPresentation := SubmersiveSplitPresentation.submersiveSplitPresentation R S P.map P.map_inj P.toPresentation
      map := id
      map_inj := Function.injective_id }

theorem submersiveSplitPrePresentation_aevalDifferential [Finite σ] :
    letI := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S P.map P.val
    (submersiveSplitPrePresentation R S P).aevalDifferential = P.aevalDifferential := by
  let := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S P.map P.val
  classical
  let := Fintype.ofFinite σ
  apply (Pi.basisFun S σ).ext
  intro j
  ext i
  rw [Pi.basisFun_apply, Algebra.PreSubmersivePresentation.aevalDifferential_single,
    Algebra.PreSubmersivePresentation.aevalDifferential_single]
  change SubmersiveSplitEvaluation.submersiveSplitEvaluation R S P.map P.val
    (MvPolynomial.pderiv i (SubmersivePolynomialSplit.submersivePolynomialSplit R P.map P.map_inj (P.relation j))) =
      MvPolynomial.aeval P.val (MvPolynomial.pderiv (P.map i) (P.relation j))
  rw [SubmersiveSplitDifferential.submersivePolynomialSplit_pderiv, SubmersiveSplitEvaluation.submersiveSplitEvaluation_apply]

theorem submersiveSplitPrePresentation_jacobian [Finite σ] :
    letI := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S P.map P.val
    (submersiveSplitPrePresentation R S P).jacobian = P.jacobian := by
  let := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S P.map P.val
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_det_aevalDifferential,
    submersiveSplitPrePresentation_aevalDifferential,
    ← Algebra.PreSubmersivePresentation.jacobian_eq_det_aevalDifferential]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveSplitJacobian
