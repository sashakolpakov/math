import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointActiveCriteria
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FactorSquares

/-! # Point Named Active Criteria -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointNamedActiveCriteria

noncomputable section

/-! Compare a proved active special kernel with a separately named
actual presentation on the point through its carrier inclusion square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FactorSquares
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PELQuotient
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointActiveCriteria

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
variable {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x)
variable (z : Targets.Lifts.EvaluatedTarget D R L b) (hbase : Lifts.ResidueCompatible D R b residueIso)

variable {n : ℕ} {Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) (Spec (.of R))}
variable (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (ActionFamilyComparison.Family.actionFamily l.actionData).abelian Q)
variable (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny
  ((ActionFamilyComparison.Family.actionFamily l.actionData).pullback (IntegralComparison.genericMap (R := R) (K := L)))
  ((ActionFamilyComparison.Family.actionFamily z.actionData).pullback (IntegralComparison.genericMap (R := R) (K := L))) n)
variable (hk : QuotientComparison.SameKernel (p.pullback (IntegralComparison.genericMap (R := R) (K := L))) g.isogeny)
variable (hnN : Nat.Coprime n N)
variable (hkernel : ∀ (T : Over (Spec (.of R))) (a : T ⟶ (ActionFamilyComparison.Family.actionFamily l.actionData).abelian.scheme),
  a ≫ p.hom = 1 → a ^ n = 1)

theorem evaluatedPointIsogeny_named_active_factor (r : NumberField.RingOfIntegers E)
    (H : Intrinsic.Neighbors.KernelPresentation ((ActionFamilyComparison.Family.actionFamily l.actionData).pullback
      (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).abelian.scheme)
    (hc : ∀ (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
      (a : T ⟶ ((ActionFamilyComparison.Family.actionFamily l.actionData).pullback
        (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).abelian.scheme),
      a ≫ (Over.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map (l.action.map r) = a →
      (a ≫ (p.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).hom = 1 ↔
        ∃ h : T ⟶ H.carrier, h ≫ H.inclusion = a))
    (K : Intrinsic.Neighbors.KernelPresentation (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x)).abelian.scheme)
    (e : H.carrier ≅ K.carrier)
    (he : e.hom ≫ K.inclusion = H.inclusion ≫ l.geometricFamilyIso.abelian.hom)
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (a : T ⟶ (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x)).abelian.scheme)
    (ha : a ≫ (D.pointDatum x).data.action.map r = a) :
    a ≫ (PointIsogeny.Lifts.evaluatedPointIsogeny l z hbase p g hk hnN hkernel).isogeny.hom = 1 ↔
      ∃ h : T ⟶ K.carrier, h ≫ K.inclusion = a :=
  (PointActiveCriteria.evaluatedPointIsogeny_active_factor l z hbase p g hk hnN hkernel r H hc T a ha).trans
    (Kernel.FactorSquares.factor_iff_of_carrier_iso e (H.inclusion ≫ l.geometricFamilyIso.abelian.hom) K.inclusion he a)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointNamedActiveCriteria
