import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescription
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

/-! # Prescribed Block Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedBlockBaseChange.Construction

noncomputable section

/-! The independent prescribed block component retains the actual
integral projector under arbitrary source field base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k k' : Type} [Field k] [Field k']
variable {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (s : Spec (.of k') ⟶ Spec (.of k)) (n : ℕ) (τ : Gal(E/ℚ))

theorem prescribedBlockComponent_baseChange (Q : Over (Spec (.of k')))
    (x : ((A.pullback s).abelian.torsionFunctor (q ^ n)).obj (.op Q)) :
    A.abelian.torsionBaseChangeEquiv s Q (q ^ n)
      (Prescription.Construction.prescribedBlockComponent j iota hsplit (A.pullback s) (ρ.pullback s) n τ Q x) =
      Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ ((Over.map s).obj Q)
        (A.abelian.torsionBaseChangeEquiv s Q (q ^ n) x) := by
  apply Subtype.ext
  exact TestBaseChangePoints.Construction.baseChangePoints_postcomp A.abelian s A.abelian
    (ρ.map (j.projector iota hsplit n τ)) Q x.val

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedBlockBaseChange.Construction
