import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointActiveData

/-! # Point Block Levels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The native point-data source comparison commutes with the original
torsion-level embeddings. -/

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

theorem Integral.Construction.SplitPELReduction.pointFrobeniusBlockSourceIso_level (x : D.OrdinaryPoint) (τ : Gal(E/ℚ))
    {n m : ℕ} (hnm : n ≤ m) :
    CMPointsAt.Construction.l45BlockLevelEmbedding j iota' hsplit
      ((D.pointDatum x.val).data.polarized.abelian.pullback D.nativeIntegralGeometricFrobenius.left)
      ((D.pointDatum x.val).data.action.pullback D.nativeIntegralGeometricFrobenius.left) τ hnm ≫
        (D.pointFrobeniusBlockSourceIso j iota' hsplit x m τ).hom =
      (D.pointFrobeniusBlockSourceIso j iota' hsplit x n τ).hom ≫
        CMPointsAt.Construction.l45BlockLevelEmbedding j iota' hsplit
          (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian
          (D.pointDatum (D.ordinaryFrobenius x).val).data.action τ hnm :=
  EquivariantBlockIso.Construction.equivariantAbelianBlockIso_level j iota' hsplit
    ((D.pointDatum x.val).data.polarized.abelian.pullback D.nativeIntegralGeometricFrobenius.left)
    (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian
    ((D.pointDatum x.val).data.action.pullback D.nativeIntegralGeometricFrobenius.left)
    (D.pointDatum (D.ordinaryFrobenius x).val).data.action
    (D.ordinaryPointFrobeniusAbelianComparison x) τ hnm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
