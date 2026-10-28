import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Reduction
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TargetReduction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryQuotients

/-! # Quotients -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated

noncomputable section

/-!
Connect the independently evaluated and properly extended native target
to the quotient by the integral neighbor kernel. The comparison is
constructed from the generic isogeny and HomExtension, then specialized; no target
identification is an input.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryQuotients.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TargetReduction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
variable {b : B.R →+* R}
variable {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}

def Quotients.Lifts.geometricClosedBase : Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫ Lifts.closedBase R

variable (z : Targets.Lifts.EvaluatedTarget D R L b) (hbase : Lifts.ResidueCompatible D R b residueIso)

/-- The special native family is the geometric fiber of the independently
extended integral family, including all polarized level data. -/
def Targets.Lifts.EvaluatedTarget.integralGeometricPolarizedIso : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
    (z.polarized.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso)))
    (D.integral.universal.data.polarized.pullback
      ((z.specialPoint hbase).left ≫ D.specialProjection)) := by
  have e := AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp D.integral.universal.data.polarized
    z.extension (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))
  have h : Quotients.Lifts.geometricClosedBase (residueIso := residueIso) ≫ z.extension =
      (z.specialPoint hbase).left ≫ D.specialProjection :=
    (Category.assoc _ _ _).trans (z.specialPoint_projection hbase).symm
  rw [h] at e
  exact e

variable {x : D.GeometricPoint}
variable (l : Lifts.IntegralLift D R b residueIso x)
variable {Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) (Spec (.of R))}

/-- The target of an evaluated generic isogeny specializes to the actual
kernel quotient whenever its integral kernel quotient has been constructed.
The generic same-kernel assertion is the kernel definition of the neighbor;
the special target comparison is a conclusion. -/
theorem Targets.Lifts.EvaluatedTarget.evaluated_reduction_is_kernel_quotient
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny l.polarized.abelian Q)
    [LocallyOfFinitePresentation p.hom.left]
    (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (l.polarized.abelian.pullback (IntegralComparison.genericMap (K := L)))
      (z.polarized.abelian.pullback (IntegralComparison.genericMap (K := L))))
    (hk : QuotientComparison.SameKernel (p.pullback (IntegralComparison.genericMap (K := L))) g)
    {H : Over (Spec (.of R))} (i : H ⟶ l.polarized.abelian.scheme) [Mono i]
    (hkernel : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel p.hom i) :
    QuotientGraphs.reducedQuotientTarget (Quotients.Lifts.geometricClosedBase (residueIso := residueIso)) i =
      Quotient.mk _ ((AbelianScheme.FrobeniusKernel.BaseChange.Construction.fppfPoints (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)))).obj
        (D.integral.universal.data.polarized.pullback
          ((z.specialPoint hbase).left ≫ D.specialProjection)).abelian.scheme) := by
  refine (TargetReduction.goodTarget_reduction_is_kernel_quotient p g hk i hkernel
    (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).trans ?_
  apply Quotient.sound
  exact ⟨(AbelianScheme.FrobeniusKernel.BaseChange.Construction.fppfPoints _).mapIso (z.integralGeometricPolarizedIso hbase).abelian⟩

/-- Ordinary rank is inherited by the actual evaluated target from the
finite source torsion. No torsion tower or target ordinarity is assumed. -/
theorem Targets.Lifts.EvaluatedTarget.evaluated_reduction_qRank
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny l.polarized.abelian Q)
    (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (l.polarized.abelian.pullback (IntegralComparison.genericMap (K := L)))
      (z.polarized.abelian.pullback (IntegralComparison.genericMap (K := L))))
    (hk : QuotientComparison.SameKernel (p.pullback (IntegralComparison.genericMap (K := L))) g)
    [IsFinite ((l.polarized.abelian.pullback
      (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).torsionScheme q).hom] :
    Nat.card ((l.polarized.abelian.pullback
      (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).torsionPoints q (Over.mk (𝟙 _))) =
    Nat.card ((z.polarized.abelian.pullback
      (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).torsionPoints q (Over.mk (𝟙 _))) :=
  AbelianScheme.FrobeniusKernel.OrdinaryQuotients.Construction.isogeny_qRank_preserved _ _
    ((TargetReduction.extendedNeighborIsogeny p g hk).pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))) q

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated
