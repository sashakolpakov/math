import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointIsogeny
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SameKernelBaseChange

/-! # Point Kernel Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointKernelComparison

noncomputable section

/-! The kernel of the constructed special PEL isogeny is the original
integral quotient kernel on the special fiber, transported through the
actual comparison with the source point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointIsogeny.Lifts
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PELQuotient
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TargetReduction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SameKernelBaseChange

private theorem kernel_comp_targetIso_iff {S : Scheme.{0}} {A B C : Over S}
    [GrpObj B] [GrpObj C] (f : A ⟶ B) (e : B ≅ C) [IsMonHom e.hom]
    (T : Over S) (a : T ⟶ A) : a ≫ (f ≫ e.hom) = 1 ↔ a ≫ f = 1 := by
  constructor
  · intro h
    apply (cancel_mono e.hom).mp
    rw [MonObj.one_comp, Category.assoc]
    exact h
  · intro h
    rw [← Category.assoc, h, MonObj.one_comp]

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

theorem evaluatedPointIsogeny_kernel_iff (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (a : T ⟶ (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x)).abelian.scheme) :
    a ≫ (PointIsogeny.Lifts.evaluatedPointIsogeny l z hbase p g hk hnN hkernel).isogeny.hom = 1 ↔
      (a ≫ l.geometricFamilyIso.abelian.inv) ≫
        (p.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).hom = 1 := by
  have hs := SameKernelBaseChange.sameKernel_pullback p (TargetReduction.extendedNeighborIsogeny p g.isogeny hk)
    (Quotients.Lifts.geometricClosedBase (residueIso := residueIso)) (PELQuotient.extendedNeighbor_sameKernel p g hk)
  have ht := @kernel_comp_targetIso_iff _ _ _ _ _ _
    (PELQuotient.evaluatedSpecialPELIsogeny p g hk hnN hkernel
      (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).isogeny.hom
    (z.geometricFamilyIso hbase).abelian (z.geometricFamilyIso hbase).abelianGroup
    T (a ≫ l.geometricFamilyIso.abelian.inv)
  rw [PointIsogeny.Lifts.evaluatedPointIsogeny, AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.transport_hom]
  apply Iff.trans ?_ (hs T (a ≫ l.geometricFamilyIso.abelian.inv)).symm
  simpa only [Category.assoc, AbelianScheme.TateComparison.PELModuli.PELFamilyIso.symm, Iso.symm_hom, PELQuotient.evaluatedSpecialPELIsogeny,
    PELIsogenySpecialization.specialPELIsogeny] using ht

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointKernelComparison
