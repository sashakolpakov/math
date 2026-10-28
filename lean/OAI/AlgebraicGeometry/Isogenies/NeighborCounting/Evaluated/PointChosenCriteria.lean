import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointKernelComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.SourceAction

/-! # Point Chosen Criteria -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointChosenCriteria

noncomputable section

/-! Transport the proved chosen-component criterion of an integral
quotient to its actual special PEL point isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PELQuotient
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointKernelComparison

private theorem comp_iso_pow_eq_one {S : Scheme.{0}} {A B : Over S}
    [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom]
    (T : Over S) (a : T ⟶ A) (m : ℕ) : (a ≫ e.hom) ^ m = 1 ↔ a ^ m = 1 := by
  constructor
  · intro h
    apply (cancel_mono e.hom).mp
    rw [MonObj.pow_comp, MonObj.one_comp]
    exact h
  · intro h
    rw [← MonObj.pow_comp, h, MonObj.one_comp]

private theorem comp_iso_eq_one {S : Scheme.{0}} {A B : Over S}
    [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom]
    (T : Over S) (a : T ⟶ A) : a ≫ e.hom = 1 ↔ a = 1 := by
  simpa only [pow_one] using comp_iso_pow_eq_one e T a 1

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

theorem evaluatedPointIsogeny_compact_iff (r : NumberField.RingOfIntegers E) (flag : Bool)
    (hc : ∀ (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
      (a : T ⟶ ((ActionFamilyComparison.Family.actionFamily l.actionData).pullback
        (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).abelian.scheme),
      a ≫ (Over.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map (l.action.map r) = a →
      (a ≫ (p.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).hom = 1 ↔
        if flag then a ^ n = 1 else a = 1))
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (a : T ⟶ (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x)).abelian.scheme)
    (ha : a ≫ (D.pointDatum x).data.action.map r = a) :
    a ≫ (PointIsogeny.Lifts.evaluatedPointIsogeny l z hbase p g hk hnN hkernel).isogeny.hom = 1 ↔
      if flag then a ^ n = 1 else a = 1 := by
  have hf := PointKernelComparison.evaluatedPointIsogeny_kernel_iff l z hbase p g hk hnN hkernel T a
  have hi := hc T (a ≫ l.geometricFamilyIso.abelian.inv)
    (l.geometricSource_action_fixed r T a ha)
  apply (hf.trans hi).trans
  cases flag
  · exact @comp_iso_eq_one _ _ _ _ _ l.geometricFamilyIso.symm.abelian
      l.geometricFamilyIso.symm.abelianGroup T a
  · exact @comp_iso_pow_eq_one _ _ _ _ _ l.geometricFamilyIso.symm.abelian
      l.geometricFamilyIso.symm.abelianGroup T a n

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointChosenCriteria
