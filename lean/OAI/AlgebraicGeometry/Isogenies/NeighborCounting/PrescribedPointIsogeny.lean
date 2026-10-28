import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELKernelTargetTransport
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedMapKernel
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification

/-! # Prescribed Point Isogeny -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedPointIsogeny

noncomputable section

/-! The independent prescribed quotient gives a full positive PEL
isogeny into its literal ordinary target point, preserving its full kernel. -/
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

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELKernelTargetTransport

variable {x y : D.OrdinaryPoint} {m : ℕ}
  {kernel : ∀ (T : Over D.integralGeometricBase.left),
    (T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) → Prop}
  (Q : D.PrescribedOrdinaryQuotient x m kernel y)

def prescribedTargetPointIso :
    PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso Q.quotient.target.data (D.pointDatum y.val).data :=
  ((Classical.choice Q.classifies).toActionIso.trans
    (PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.pullbackId Q.quotient.target.data)).symm

def prescribedPointIsogeny :
    AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x.val))
      (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum y.val)) m :=
  (Intrinsic.QuotientTargets.witnessIsogeny Q.quotient).transport (AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl _)
    (ActionFamilyComparison.Family.actionIsoToFamilyIso (prescribedTargetPointIso Q))

theorem prescribedPointIsogeny_kernel :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (prescribedPointIsogeny Q).isogeny.hom Q.inclusion :=
  PELKernelTargetTransport.prescribedKernel_target_transport (Intrinsic.QuotientTargets.witnessIsogeny Q.quotient)
    (ActionFamilyComparison.Family.actionIsoToFamilyIso (prescribedTargetPointIso Q)) Q.inclusion Q.quotient.kernel

theorem prescribedPointIsogeny_kernel_iff
    (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) :
    a ≫ (prescribedPointIsogeny Q).isogeny.hom = 1 ↔ kernel T a := by
  have : IsClosedImmersion Q.inclusion.left := Q.closed
  have : Mono Q.inclusion := Over.mono_of_mono_left _
  constructor
  · intro ha
    obtain ⟨h, hh, _⟩ := (prescribedPointIsogeny_kernel Q T a).mp ha
    exact (Q.realizes T a).mp ⟨h, hh⟩
  · intro ha
    obtain ⟨h, hh⟩ := (Q.realizes T a).mpr ha
    apply (prescribedPointIsogeny_kernel Q T a).mpr
    exact ⟨h, hh, fun b hb => (cancel_mono Q.inclusion).mp (hb.trans hh.symm)⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedPointIsogeny
