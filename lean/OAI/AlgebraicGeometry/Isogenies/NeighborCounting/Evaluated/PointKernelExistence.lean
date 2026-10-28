import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointIsogeny

/-! # Point Kernel Existence -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointKernelExistence

noncomputable section

/-! Construct the special PEL isogeny and its complete kernel together
from the actual integral isogeny and its original inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointIsogeny.Lifts
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PELQuotient
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison

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

include g hk hnN hkernel in
theorem pointIsogeny_exists_kernel {H : Over (Spec (.of R))}
    (i : H ⟶ (ActionFamilyComparison.Family.actionFamily l.actionData).abelian.scheme) (hi : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel p.hom i) :
    ∃ f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x))
      (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum (z.specialPoint hbase))) n,
      AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel f.isogeny.hom
        ((Over.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map i ≫
          l.geometricFamilyIso.abelian.hom) :=
  ⟨PointIsogeny.Lifts.evaluatedPointIsogeny l z hbase p g hk hnN hkernel,
    PointIsogeny.Lifts.evaluatedPointIsogeny_kernel l z hbase p g hk hnN hkernel i hi⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointKernelExistence
