import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveSplitJacobian
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-! # Submersive Etale Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveEtaleCoordinates

noncomputable section

/-! A submersive presentation is étale over the polynomial algebra in the unselected variables. -/

universe u v w t

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {ι : Type w} {σ : Type t} [Finite σ] (P : Algebra.SubmersivePresentation R S ι σ)

def submersiveEtalePresentation :
    letI := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S P.map P.val
    Algebra.SubmersivePresentation (MvPolynomial (SubmersivePolynomialSplit.UnselectedVariables P.map) R) S σ σ := by
  letI := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S P.map P.val
  exact
    { toPreSubmersivePresentation := SubmersiveSplitJacobian.submersiveSplitPrePresentation R S P.toPreSubmersivePresentation
      jacobian_isUnit :=
        (SubmersiveSplitJacobian.submersiveSplitPrePresentation_jacobian R S P.toPreSubmersivePresentation).symm ▸
          P.jacobian_isUnit }

theorem submersiveEtalePresentation_dimension :
    letI := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S P.map P.val
    (submersiveEtalePresentation R S P).dimension = 0 := by
  simp only [Algebra.Presentation.dimension, Nat.sub_self]

theorem submersiveEtaleCoordinates :
    letI := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S P.map P.val
    Algebra.Etale (MvPolynomial (SubmersivePolynomialSplit.UnselectedVariables P.map) R) S := by
  let := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S P.map P.val
  have : Algebra.IsStandardSmoothOfRelativeDimension 0
      (MvPolynomial (SubmersivePolynomialSplit.UnselectedVariables P.map) R) S :=
    (submersiveEtalePresentation R S P).isStandardSmoothOfRelativeDimension
      (submersiveEtalePresentation_dimension R S P)
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveEtaleCoordinates
