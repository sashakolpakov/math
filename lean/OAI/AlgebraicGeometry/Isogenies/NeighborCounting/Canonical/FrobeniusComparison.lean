import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusPEL
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedPointIsogeny
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification

/-! # Frobenius Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.FrobeniusComparison.X

noncomputable section

/-! The independent X quotient and the actual native Frobenius have
the same full kernel. Their constructed full PEL quotient isomorphism
supplies the actual Frobenius comparison for the mixed operators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusPEL OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedPointIsogeny OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELTargetComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  (C0 : D.CompactKernelPrescription j iota hsplit labels)
  {x y : D.OrdinaryPoint}
  (QX : D.PrescribedOrdinaryQuotient x q (D.prescribedFullXKernel j iota hsplit labels O C0 x) y)
  (hFrob : ∀ (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
    D.prescribedFullXKernel j iota hsplit labels O C0 x T a ↔ D.relativeFrobeniusKernelCondition x T a)

include hFrob in
theorem canonicalXFrobeniusSameKernel :
    QuotientComparison.SameKernel (Intrinsic.FrobeniusPEL.nativeFrobeniusPEL (D.pointDatum x.val)).isogeny (PrescribedPointIsogeny.prescribedPointIsogeny QX).isogeny := by
  intro T a
  have hq := PrescribedPointIsogeny.prescribedPointIsogeny_kernel_iff QX T a
  have hf := hFrob T a
  have hn := Iff.of_eq (congrArg (fun f => a ≫ f = 1) (Intrinsic.FrobeniusPEL.nativeFrobeniusPEL_hom (D.pointDatum x.val)))
  exact hn.trans (hq.trans hf).symm

def canonicalXFrobeniusIso :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso (Intrinsic.QuotientTargets.geometricFamily ((D.pointDatum x.val).pullback D.nativeIntegralGeometricFrobenius))
      (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum y.val)) :=
  PELTargetComparison.quotientPELIso (Intrinsic.FrobeniusPEL.nativeFrobeniusPEL (D.pointDatum x.val)) (PrescribedPointIsogeny.prescribedPointIsogeny QX)
    (canonicalXFrobeniusSameKernel j hsplit labels O C0 QX hFrob)

def canonicalXFrobeniusComparison :
    AbelianScheme.FrobeniusKernel.PolarizedComponents.Construction.EquivariantAbelianIso
      (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) (D.pointDatum x.val).data.polarized.abelian)
      (D.pointDatum y.val).data.polarized.abelian
      (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
        (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action)
      (D.pointDatum y.val).data.action :=
  let e := ActionFamilyComparison.Family.familyIsoToActionIso (canonicalXFrobeniusIso j hsplit labels O C0 QX hFrob)
  { abelian := e.polarized.abelian
    preservesGroup := e.polarized.abelianGroup
    action := e.action }

private theorem projection_of_hom {R k : Type} [CommRing R] [Field k] [IsAlgClosed k] {d N n : ℕ}
    {A B C : AbelianScheme.TateComparison.PEL.PELFamilyData R d N (Spec (.of k))} (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A B n) (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A C n)
    (hk : QuotientComparison.SameKernel f.isogeny g.isogeny) (f0 : A.abelian.scheme ⟶ B.abelian.scheme)
    (hf : f.isogeny.hom = f0) : f0 ≫ (PELTargetComparison.quotientPELIso f g hk).abelian.hom = g.isogeny.hom :=
  (congrArg (fun u => u ≫ (PELTargetComparison.quotientPELIso f g hk).abelian.hom) hf).symm.trans
    (PELTargetComparison.quotientPELIso_projection f g hk)

theorem canonicalXFrobenius_projection :
    (AbelianScheme.FrobeniusKernel.Action.Construction.frobeniusIsogeny q (Fact.out : q.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q))
      (D.pointDatum x.val).data.polarized.abelian).hom ≫
        (canonicalXFrobeniusComparison j hsplit labels O C0 QX hFrob).abelian.hom =
      (PrescribedPointIsogeny.prescribedPointIsogeny QX).isogeny.hom :=
  projection_of_hom (Intrinsic.FrobeniusPEL.nativeFrobeniusPEL (D.pointDatum x.val)) (PrescribedPointIsogeny.prescribedPointIsogeny QX)
    (canonicalXFrobeniusSameKernel j hsplit labels O C0 QX hFrob) _
    (Intrinsic.FrobeniusPEL.nativeFrobeniusPEL_hom (D.pointDatum x.val))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.FrobeniusComparison.X
