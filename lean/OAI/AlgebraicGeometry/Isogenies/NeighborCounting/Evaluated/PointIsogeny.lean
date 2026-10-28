import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointDataSpecialization
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PELQuotient
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.KernelIsoTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ContainmentBaseChange

/-! # Point Isogeny -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting

/-! The independent evaluated generic target reduces to the original
native geometric point. Both PEL comparison maps and the transported
complete subgroup are constructed from the integral source and target. -/

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
variable (z : Evaluated.Targets.Lifts.EvaluatedTarget D R L b) (hbase : Lifts.ResidueCompatible D R b residueIso)

def Lifts.IntegralLift.geometricFamilyIso :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso ((ActionFamilyComparison.Family.actionFamily l.actionData).pullback
      (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))) (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x)) :=
  (ActionFamilyComparison.Family.actionFamilyPullbackIso l.actionData _).trans (ActionFamilyComparison.Family.actionIsoToFamilyIso l.geometricActionIso)

def Evaluated.Targets.Lifts.EvaluatedTarget.geometricFamilyIso :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso ((ActionFamilyComparison.Family.actionFamily z.actionData).pullback
      (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso)))
      (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum (z.specialPoint hbase))) :=
  (ActionFamilyComparison.Family.actionFamilyPullbackIso z.actionData _).trans
    (ActionFamilyComparison.Family.actionIsoToFamilyIso (z.integralGeometricActionIso hbase))

variable {n : ℕ} {Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) (Spec (.of R))}
variable (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (ActionFamilyComparison.Family.actionFamily l.actionData).abelian Q)
variable (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny
  ((ActionFamilyComparison.Family.actionFamily l.actionData).pullback (IntegralComparison.genericMap (R := R) (K := L)))
  ((ActionFamilyComparison.Family.actionFamily z.actionData).pullback (IntegralComparison.genericMap (R := R) (K := L))) n)
variable (hk : QuotientComparison.SameKernel (p.pullback (IntegralComparison.genericMap (R := R) (K := L))) g.isogeny)
variable (hnN : Nat.Coprime n N)
variable (hkernel : ∀ (T : Over (Spec (.of R))) (a : T ⟶ (ActionFamilyComparison.Family.actionFamily l.actionData).abelian.scheme),
  a ≫ p.hom = 1 → a ^ n = 1)

/-- The special isogeny has the actual source and reduced target point
data, including the original positive polarization and ordered marking. -/
def Evaluated.PointIsogeny.Lifts.evaluatedPointIsogeny : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x))
    (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum (z.specialPoint hbase))) n :=
  (Evaluated.PELQuotient.evaluatedSpecialPELIsogeny p g hk hnN hkernel
    (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).transport
      l.geometricFamilyIso.symm (z.geometricFamilyIso hbase)

/-- The all-test kernel is the literal base change of the original full
integral subgroup, followed by the constructed comparison to the source point. -/
theorem Evaluated.PointIsogeny.Lifts.evaluatedPointIsogeny_kernel {H : Over (Spec (.of R))}
    (i : H ⟶ (ActionFamilyComparison.Family.actionFamily l.actionData).abelian.scheme) (hi : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel p.hom i) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (Evaluated.PointIsogeny.Lifts.evaluatedPointIsogeny l z hbase p g hk hnN hkernel).isogeny.hom
      ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map i ≫
        l.geometricFamilyIso.abelian.hom) := by
  rw [Evaluated.PointIsogeny.Lifts.evaluatedPointIsogeny, AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.transport_hom]
  exact Kernel.KernelIsoTransport.prescribedKernel_isos _ _
    (Evaluated.PELQuotient.evaluatedSpecialPELIsogeny_kernel p g hk hnN hkernel
      (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso)) i hi)
    l.geometricFamilyIso.symm.abelian (z.geometricFamilyIso hbase).abelian

def Evaluated.PointIsogeny.Lifts.evaluatedPointWitness (H : Grp (Over (Spec (.of R))))
    (i : H.X ⟶ (ActionFamilyComparison.Family.actionFamily l.actionData).abelian.scheme) (hi : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel p.hom i) :
    D.QuotientWitness (D.pointDatum x) n
      ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).mapGrp.obj H)
      ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map i ≫
        l.geometricFamilyIso.abelian.hom) :=
  PointQuotientWitness.isogenyWitness
    (Evaluated.PointIsogeny.Lifts.evaluatedPointIsogeny l z hbase p g hk hnN hkernel)
    (Evaluated.PointIsogeny.Lifts.evaluatedPointIsogeny_kernel l z hbase p g hk hnN hkernel i hi)

include g hk hnN hkernel in
/-- Equality with an independently constructed native quotient point
is a consequence of the full specialized kernel and PEL data. -/
theorem Evaluated.PointIsogeny.Lifts.independentEvaluatedTarget_point
    (hgood : D.IsGoodCompletelySplitReduction) (H : Grp (Over (Spec (.of R))))
    (i : H.X ⟶ (ActionFamilyComparison.Family.actionFamily l.actionData).abelian.scheme) (hi : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel p.hom i)
    (Q' : D.QuotientWitness (D.pointDatum x) n
      ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).mapGrp.obj H)
      ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map i ≫
        l.geometricFamilyIso.abelian.hom)) :
    D.pointOfPEL hgood Q'.target = z.specialPoint hbase :=
  PointQuotientWitness.independentQuotient_point hgood (z.specialPoint hbase)
    (Evaluated.PointIsogeny.Lifts.evaluatedPointIsogeny l z hbase p g hk hnN hkernel)
    (Evaluated.PointIsogeny.Lifts.evaluatedPointIsogeny_kernel l z hbase p g hk hnN hkernel i hi) Q'

end AlgebraicGeometry.Isogenies.NeighborCounting

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointIsogeny.KernelBound

/-! The original integral full-kernel bound survives proper extension,
base change, and both native PEL point comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PELQuotient
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TargetReduction

private theorem kernel_bound_of_isos {S : Scheme.{0}} {A B C D : Over S}
    [GrpObj A] [GrpObj B] [GrpObj C] [GrpObj D]
    (f : A ⟶ B) (e : C ≅ A) (t : B ≅ D)
    [IsMonHom e.hom] [IsMonHom t.hom] (n : ℕ)
    (hf : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
    (T : Over S) (x : T ⟶ C) (hx : x ≫ (e.hom ≫ f ≫ t.hom) = 1) : x ^ n = 1 := by
  have hk : (x ≫ e.hom) ≫ f = 1 := by
    apply (cancel_mono t.hom).mp
    rw [MonObj.one_comp]
    simpa only [Category.assoc] using hx
  apply (cancel_mono e.hom).mp
  rw [MonObj.pow_comp, MonObj.one_comp]
  exact hf T (x ≫ e.hom) hk

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
theorem evaluatedPointIsogeny_kernel_bound
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (a : T ⟶ (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x)).abelian.scheme)
    (ha : a ≫ (Lifts.evaluatedPointIsogeny l z hbase p g hk hnN hkernel).isogeny.hom = 1) :
    a ^ n = 1 := by
  have hb := Picard.PoincareBundle.Kernel.ContainmentBaseChange.contained
    (TargetReduction.extendedNeighborIsogeny p g.isogeny hk) n
    (fun U b hb => hkernel U b ((PELQuotient.extendedNeighbor_sameKernel p g hk U b).mpr hb))
    (Quotients.Lifts.geometricClosedBase (residueIso := residueIso))
  rw [Lifts.evaluatedPointIsogeny, AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.transport_hom] at ha
  exact @kernel_bound_of_isos _ _ _ _ _ _ _ _ _ _ l.geometricFamilyIso.symm.abelian
    (z.geometricFamilyIso hbase).abelian l.geometricFamilyIso.symm.abelianGroup
    (z.geometricFamilyIso hbase).abelianGroup n hb T a ha

end AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointIsogeny.KernelBound

end

end OAI
