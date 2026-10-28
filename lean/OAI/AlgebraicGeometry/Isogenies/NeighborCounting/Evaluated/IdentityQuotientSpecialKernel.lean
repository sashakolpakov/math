import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointIsogeny
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IdentityModeledQuotient

/-! # Identity Quotient Special Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.IdentityQuotientSpecialKernel

noncomputable section

/-! Specialize the complete kernel of an actual normalized modeled
quotient before inserting the original evaluation field and parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family
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

variable {n : ℕ}
  {F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup (ActionFamilyComparison.Family.actionFamily l.actionData).abelian.scheme (Over.mk (𝟙 (Spec (.of R))))}
  {FM : F.Model}
  (I : Intrinsic.ModeledQuotient.Lifts.NativeModeledQuotient (ActionFamilyComparison.Family.actionFamily l.actionData).abelian
    (Over.mk (𝟙 (Spec (.of R)))) F FM n)
  (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny
    ((ActionFamilyComparison.Family.actionFamily l.actionData).pullback (IntegralComparison.genericMap (R := R) (K := L)))
    ((ActionFamilyComparison.Family.actionFamily z.actionData).pullback (IntegralComparison.genericMap (R := R) (K := L))) n)
  (hk : QuotientComparison.SameKernel (I.identitySourceIsogeny.pullback (IntegralComparison.genericMap (R := R) (K := L))) g.isogeny)
  (hnN : Nat.Coprime n N)

def evaluatedIdentityQuotientPointKernelIdentity :=
  PLift.up (PointIsogeny.Lifts.evaluatedPointIsogeny_kernel l z hbase I.identitySourceIsogeny g hk hnN
    I.identitySourceIsogeny_kernel_bound I.identitySourceInclusion I.identitySourceIsogeny_kernel)

include g hk hnN in
theorem evaluatedIdentityQuotientPoint_kernel_exists :
    ∃ f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x))
      (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum (z.specialPoint hbase))) n,
      AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel f.isogeny.hom
        ((Over.pullback (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map I.identitySourceInclusion ≫
          l.geometricFamilyIso.abelian.hom) := by
  refine ⟨PointIsogeny.Lifts.evaluatedPointIsogeny l z hbase I.identitySourceIsogeny g hk hnN
    I.identitySourceIsogeny_kernel_bound, ?_⟩
  exact (evaluatedIdentityQuotientPointKernelIdentity l z hbase I g hk hnN).down

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.IdentityQuotientSpecialKernel
