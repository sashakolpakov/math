import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.SpecialActiveKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.PresentationComposition
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.SourceAction

/-! # Active Point Presentation -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! Embed the actual specialized active carrier in the source PEL point
and transport its geometric presentation without changing that carrier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x)

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
  (hlabels : ∀ v : Fin s, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
  (n : ℕ) (hn : 1 ≤ n) (active : Fin s) (multiplicative : Fin s → Bool)
  (H : Kernel.Properties.FiniteFlatKernel (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1)
    (l.action.map (j.projector iota hsplit 1 (labels (active, false))))))

def Lifts.IntegralLift.activePointPresentation :
    Intrinsic.Neighbors.KernelPresentation (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x)).abelian.scheme :=
  ⟨(Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).obj H.carrier,
    (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
      (H.inclusion ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1)
        (l.action.map (j.projector iota hsplit 1 (labels (active, false))))) ≫
          l.geometricFamilyIso.abelian.hom⟩

theorem Lifts.IntegralLift.activePointPresentation_special_eq
    (P : Intrinsic.Neighbors.KernelPresentation ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).obj
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (active, false)))))))
    (hP : H.toKernelPresentation.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso)) = P) :
    l.activePointPresentation j hsplit labels active H =
      P.postcomp ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (active, false))))) ≫
          l.geometricFamilyIso.abelian.hom) :=
  H.toKernelPresentation.pullback_postcomp_eq
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (active, false)))))
    (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso)) l.geometricFamilyIso.abelian.hom P hP

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
