import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointQuotient
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockSourceIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EquivariantBlockIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenSourceIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsChosenBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveSplittingSourceTransport

/-! # Point Active Data -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

section

/-! The literal point datum at Frobenius has the same native coefficient
blocks as the source pullback, with the original equivariant source isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)
variable {K' : Type} [Field K'] [NumberField K'] {κ' : K' →+* ℂ}
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K' κ' q) (iota' : E →+* K') (hsplit : j.HasSplitCoordinates iota')
variable (x : D.OrdinaryPoint) (n : ℕ) (τ : Gal(E/ℚ))

def Integral.Construction.SplitPELReduction.pointFrobeniusBlockSourceIso :
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota' hsplit
      ((D.pointDatum x.val).data.polarized.abelian.pullback D.nativeIntegralGeometricFrobenius.left)
      ((D.pointDatum x.val).data.action.pullback D.nativeIntegralGeometricFrobenius.left) n τ).toGrp ≅
      (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized
        (D.pointDatum (D.ordinaryFrobenius x).val).data.action τ n) := by
  let A0 : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme _ (Spec (.of (ModuliPoint.Construction.residueClosure q))) :=
    (D.pointDatum x.val).data.polarized.abelian
  let B0 : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme _ (Spec (.of (ModuliPoint.Construction.residueClosure q))) :=
    (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian
  exact EquivariantBlockIso.Construction.equivariantAbelianBlockIso j iota' hsplit
    (A0.pullback D.nativeIntegralGeometricFrobenius.left) B0
    ((D.pointDatum x.val).data.action.pullback D.nativeIntegralGeometricFrobenius.left)
    (D.pointDatum (D.ordinaryFrobenius x).val).data.action
    (D.ordinaryPointFrobeniusAbelianComparison x) n τ

def Integral.Construction.SplitPELReduction.pointFrobeniusBlockIso :
    (Over.pullback D.nativeIntegralGeometricFrobenius.left).mapGrp.obj
      (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum x.val).data.polarized
        (D.pointDatum x.val).data.action τ n) ≅
      CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized
        (D.pointDatum (D.ordinaryFrobenius x).val).data.action τ n :=
  ChosenSourceIso.Construction.frobeniusSourceBlockIso j iota' hsplit (ModuliPoint.Construction.residueClosure q)
    (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian
    (D.pointDatum x.val).data.action (D.pointDatum (D.ordinaryFrobenius x).val).data.action
    (D.ordinaryPointFrobeniusAbelianComparison x) n τ

end

/-! Active Frobenius transport uses the ordinary coordinates at the
actual target point, pulled through the native block source isomorphism. -/

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

def Integral.Construction.SplitPELReduction.pointFrobeniusActiveSplitting : ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting (ModuliPoint.Construction.residueClosure q) q
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota' hsplit
      (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) (ModuliPoint.Construction.residueClosure q)
        (D.pointDatum x.val).data.polarized.abelian)
      (CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) (ModuliPoint.Construction.residueClosure q)
        (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action)
      1 (labels (0, false))).toGrp :=
  ChosenSourceIso.Construction.frobeniusSourceActiveSplitting j iota' hsplit (ModuliPoint.Construction.residueClosure q)
    (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian
    (D.pointDatum x.val).data.action (D.pointDatum (D.ordinaryFrobenius x).val).data.action
    (D.ordinaryPointFrobeniusAbelianComparison x) (labels (0, false))
    (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting (ModuliPoint.Construction.residueClosure q) q (O.splitting (D.ordinaryFrobenius x) 1 0))

def Integral.Construction.SplitPELReduction.pointFrobeniusLineEquiv : EtaleSubgroups.Construction.ActiveEtaleLine q ≃ EtaleSubgroups.Construction.ActiveEtaleLine q :=
  CMPointsLines.Construction.l45FrobeniusLineEquiv j iota' hsplit (ModuliPoint.Construction.residueClosure q)
    (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action
    (labels (0, false)) (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting (ModuliPoint.Construction.residueClosure q) q (O.splitting x 1 0))
    (D.pointFrobeniusActiveSplitting j iota' hsplit labels O x)

def Integral.Construction.SplitPELReduction.pointFrobeniusLineBaseChangeIso (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (Over.pullback D.nativeIntegralGeometricFrobenius.left).obj
      (EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of (ModuliPoint.Construction.residueClosure q))) q L).X ≅
    (EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of (ModuliPoint.Construction.residueClosure q))) q
      (D.pointFrobeniusLineEquiv j iota' hsplit labels O x L)).X :=
  PointsChosenBaseChange.Construction.l45FrobeniusLineBaseChangeIso j iota' hsplit (ModuliPoint.Construction.residueClosure q)
    (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action
    (labels (0, false)) (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting (ModuliPoint.Construction.residueClosure q) q (O.splitting x 1 0))
    (D.pointFrobeniusActiveSplitting j iota' hsplit labels O x) L

def Integral.Construction.SplitPELReduction.pointFrobeniusPlaneBaseChangeIso :
    (Over.pullback D.nativeIntegralGeometricFrobenius.left).obj
      (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of (ModuliPoint.Construction.residueClosure q))) q).X ≅
    (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of (ModuliPoint.Construction.residueClosure q))) q).X :=
  PointsChosenBaseChange.Construction.l45FrobeniusPlaneBaseChangeIso j iota' hsplit (ModuliPoint.Construction.residueClosure q)
    (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action
    (labels (0, false)) (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting (ModuliPoint.Construction.residueClosure q) q (O.splitting x 1 0))
    (D.pointFrobeniusActiveSplitting j iota' hsplit labels O x)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
