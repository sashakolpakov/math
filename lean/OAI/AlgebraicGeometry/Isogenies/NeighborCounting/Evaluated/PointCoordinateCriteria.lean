import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FixedKernelCriterion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointActiveCriteria
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinatePresentationFactorTransport
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FactorSquares
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointKernelComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.SourceAction
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SpecialKernelPresentations

/-! # Point Coordinate Criteria -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointCoordinateCriteria

noncomputable section

/-! Transport an actual specialized active-kernel presentation through
the original geometric source comparison to the special PEL point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PELQuotient
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointKernelComparison

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

attribute [local instance] Classical.propDecidable

theorem evaluatedPointIsogeny_coordinate_factor (r : NumberField.RingOfIntegers E)
    (H : Intrinsic.Neighbors.KernelPresentation ((ActionFamilyComparison.Family.actionFamily l.actionData).pullback
      (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).abelian.scheme)
    (hc : ∀ (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
      (a : T ⟶ ((ActionFamilyComparison.Family.actionFamily l.actionData).pullback
        (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).abelian.scheme),
      a ≫ (Over.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map (l.action.map r) = a →
      (a ≫ (p.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).hom = 1 ↔
        ∃ h : T ⟶ H.carrier, h ≫ H.inclusion = a))
    {G : Grp (Over (Spec (.of R)))} (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q G)
    (i : G.X ⟶ (ActionFamilyComparison.Family.actionFamily l.actionData).abelian.scheme)
    (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q))
    (V : Submodule (ZMod q) (Fin 2 → ZMod q)) (flag : Bool)
    (hV : J.map (LinearMap.fst (ZMod q) (Fin 2 → ZMod q) (ZMod q)) = V)
    (hflag : decide (SubspaceCounts.Construction.identityLine ≤ J) = flag)
    (hH : H = ((C.finiteFlatKernel R L q G J).toKernelPresentation.postcomp i).pullback
      (Quotients.Lifts.geometricClosedBase (residueIso := residueIso)))
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (a : T ⟶ (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x)).abelian.scheme)
    (ha : a ≫ (D.pointDatum x).data.action.map r = a) :
    let Q := (C.geometricSpecialKernel R L q G residueIso V flag).postcomp
      ((Over.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map i ≫
        l.geometricFamilyIso.abelian.hom)
    a ≫ (PointIsogeny.Lifts.evaluatedPointIsogeny l z hbase p g hk hnN hkernel).isogeny.hom = 1 ↔
      ∃ h : T ⟶ Q.carrier, h ≫ Q.inclusion = a := by
  have h := PointActiveCriteria.evaluatedPointIsogeny_active_factor
    l z hbase p g hk hnN hkernel r H hc T a ha
  have he := Intrinsic.Neighbors.KernelPresentation.factor_iff_of_eq _ _ hH l.geometricFamilyIso.abelian.hom T a
  have hf := C.finiteFlatKernel_geometric_presentation_factor R L q G residueIso
    i l.geometricFamilyIso.abelian.hom J V flag hV hflag T a
  exact h.trans (he.trans hf)

theorem evaluatedPointIsogeny_coordinate_criterion (r : NumberField.RingOfIntegers E)
    (H : Intrinsic.Neighbors.KernelPresentation ((ActionFamilyComparison.Family.actionFamily l.actionData).pullback
      (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).abelian.scheme)
    (hc : ∀ (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
      (a : T ⟶ ((ActionFamilyComparison.Family.actionFamily l.actionData).pullback
        (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).abelian.scheme),
      a ≫ (Over.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map (l.action.map r) = a →
      (a ≫ (p.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).hom = 1 ↔
        ∃ h : T ⟶ H.carrier, h ≫ H.inclusion = a))
    {G : Grp (Over (Spec (.of R)))} (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q G)
    (i : G.X ⟶ (ActionFamilyComparison.Family.actionFamily l.actionData).abelian.scheme)
    (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q))
    (V : Submodule (ZMod q) (Fin 2 → ZMod q)) (flag : Bool)
    (hV : J.map (LinearMap.fst (ZMod q) (Fin 2 → ZMod q) (ZMod q)) = V)
    (hflag : decide (SubspaceCounts.Construction.identityLine ≤ J) = flag)
    (hH : H = ((C.finiteFlatKernel R L q G J).toKernelPresentation.postcomp i).pullback
      (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))) :
    ((C.geometricSpecialKernel R L q G residueIso V flag).postcomp
      ((Over.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map i ≫
        l.geometricFamilyIso.abelian.hom)).KernelOnFixed
      (PointIsogeny.Lifts.evaluatedPointIsogeny l z hbase p g hk hnN hkernel).isogeny.hom
      ((D.pointDatum x).data.action.map r) :=
  evaluatedPointIsogeny_coordinate_factor l z hbase p g hk hnN hkernel r H hc
    C i J V flag hV hflag hH

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointCoordinateCriteria
