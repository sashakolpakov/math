import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointActiveData

/-! # Point Block Eq -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Object-level identification of the point block isomorphism with
the generic equivariant Frobenius construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)
variable {K' : Type} [Field K'] [NumberField K'] {κ' : K' →+* ℂ}
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K' κ' q) (iota' : E →+* K') (hsplit : j.HasSplitCoordinates iota')

theorem Integral.Construction.SplitPELReduction.pointFrobeniusBlockIso_eq_source (x : D.OrdinaryPoint) (n : ℕ) (τ : Gal(E/ℚ)) :
    D.pointFrobeniusBlockIso j iota' hsplit x n τ =
      ChosenSourceIso.Construction.frobeniusSourceBlockIso j iota' hsplit (ModuliPoint.Construction.residueClosure q)
        (D.pointDatum x.val).data.polarized.abelian
        (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian
        (D.pointDatum x.val).data.action (D.pointDatum (D.ordinaryFrobenius x).val).data.action
        (D.ordinaryPointFrobeniusAbelianComparison x) n τ := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
