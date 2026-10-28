import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationCancellation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Products

/-! # Fine Target -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! An actual PEL quotient of a family with universal global functions
has its full fine-moduli target, with uniquely determined polarization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {d N n : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))} {A B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T}
  (f : Intrinsic.PELBaseChange.Construction.NativePELQuotient A B n) (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A.polarized.abelian.scheme)
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)

def Intrinsic.PELBaseChange.Construction.NativePELQuotient.universalFunctionFineTarget : IntrinsicFineTargetData.Construction.NativeFinePELTarget A n M where
  target := FinePELTarget.Construction.finePELClassifyingMap M hM B
  isogeny := FinePELTarget.Construction.finePELClassifyingIsogeny M hM B f.isogeny
  etale := by
    have : Etale f.isogeny.hom.left := f.etale
    exact FinePELTarget.Construction.finePELClassifyingIsogeny_etale M hM B f.isogeny
  polarization := (FinePELPolarization.Construction.finePELClassifyingIsogeny_polarization_pullback M hM B A.polarized.dual f.isogeny).trans
    f.polarization
  action := FinePELTarget.Construction.finePELClassifyingIsogeny_action M hM B f.isogeny A.action f.action
  marking := FinePELTarget.Construction.finePELClassifyingIsogeny_marking M hM B f.isogeny A.polarized.level f.marking
  polarization_unique ε r hr := by
    have hB := GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source f.isogeny.hom hA
    have htarget := hB.of_iso (FinePELTarget.Construction.finePELClassifyingIso M hM B).abelian.symm
    apply PolarizationAssembly.Construction.isogeny_eq_of_hom_eq
    apply UniversalFunction.PolarizationCancellation.Construction.universalFunction_polarizationPullback_injective
      (FinePELTarget.Construction.finePELClassifyingIsogeny M hM B f.isogeny) A.polarized.dual _ htarget
    exact hr.trans ((FinePELPolarization.Construction.finePELClassifyingIsogeny_polarization_pullback M hM B A.polarized.dual f.isogeny).trans
      f.polarization).symm

theorem Intrinsic.PELBaseChange.Construction.NativePELQuotient.universalFunctionFineTarget_kernel :
    Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (f.universalFunctionFineTarget hA M hM).isogeny.hom = Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.isogeny.hom :=
  FinePELTarget.Construction.finePELClassifyingIsogeny_kernel M hM B f.isogeny

theorem Intrinsic.PELBaseChange.Construction.NativePELQuotient.universalFunctionFineTarget_tate_preimage (U : Over T.left) (q : ℕ) [Fact q.Prime] :
    TateComparison.Rational.isogenyTatePreimage (T := U) (q := q) (f.universalFunctionFineTarget hA M hM).isogeny.hom =
      TateComparison.Rational.isogenyTatePreimage (T := U) (q := q) f.isogeny.hom :=
  TateTransport.Construction.finePELClassifyingIsogeny_tate_preimage M hM B f.isogeny U q

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
