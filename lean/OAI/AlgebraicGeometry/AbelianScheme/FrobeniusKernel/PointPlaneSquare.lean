import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenSourceIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointActiveData
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointBlockLevels

/-! # Point Plane Square -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The original active q-plane has an embedded Frobenius pullback
square in q-squared torsion at the actual target point. -/

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
variable (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
variable (O : D.OrdinaryKernelData j iota' hsplit labels) (x : D.OrdinaryPoint)

theorem Integral.Construction.SplitPELReduction.pointFrobeniusPlaneBaseChangeIso_levelTwo :
    (D.pointFrobeniusPlaneBaseChangeIso j iota' hsplit labels O x).hom ≫
      D.pointActivePlaneInclusion j iota' hsplit labels O (D.ordinaryFrobenius x) =
    (Over.pullback D.nativeIntegralGeometricFrobenius.left).map
      (D.pointActivePlaneInclusion j iota' hsplit labels O x) ≫
      (D.pointFrobeniusBlockIso j iota' hsplit x 2 (labels (0, false))).hom.hom.hom :=
  ChosenSourceIso.Construction.frobeniusSourcePlaneBaseChangeIso_levelTwo j iota' hsplit (ModuliPoint.Construction.residueClosure q)
    (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian
    (D.pointDatum x.val).data.action (D.pointDatum (D.ordinaryFrobenius x).val).data.action
    (D.ordinaryPointFrobeniusAbelianComparison x) (labels (0, false))
    (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting (ModuliPoint.Construction.residueClosure q) q (O.splitting x 1 0))
    (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting (ModuliPoint.Construction.residueClosure q) q (O.splitting (D.ordinaryFrobenius x) 1 0))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
