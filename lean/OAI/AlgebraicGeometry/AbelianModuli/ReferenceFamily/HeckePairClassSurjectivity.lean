import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.HeckeObjectClassifier
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HeckePairRecovery

/-! # Hecke Pair Class Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The constructed finite etale parameter classifies every typed
paired PEL isomorphism class on every ground-base test scheme. The
comparison is a complete PEL isomorphism of the original families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (Z : Models.FinePELModel P iota N) (hZ : Z.IsFine) [IsLocallyNoetherian Z.space.left]
    {hn : 0 < n} (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (R : NoetherianPairedHeckeSource.PairedHeckeSource Z.universal n hn M)

def HeckePairClassSurjectivity.pairedHeckeObjectRecoveryIso {X : Over (Spec (.of K))}
    (B : Paired.PELFunctor.PairedPELObject P iota N n X)
    (hM : (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel B.quotient.forward.isogeny.hom).HasModuleType M) :
    Paired.PELFunctor.PairedPELQuotientIso
      (R.quotient.pullback (Paired.HeckeObjectClassifier.pairedHeckeObjectClassifyingMap Z hZ hdegree M R B hM)) B.quotient := by
  let t := Paired.HeckeObjectClassifier.pairedHeckeObjectSource Z hZ B
  let e := Paired.HeckeObjectClassifier.pairedHeckeObjectSourceIso Z hZ B
  let k := Paired.HeckeObjectClassifier.pairedHeckeObjectKernelMap Z hZ hdegree M R B hM
  let r := R.pairIsoOfClassifier (Over.mk t.left) (B.target.overSourceParameter t)
    (Paired.HeckeObjectClassifier.pairedHeckeObjectAligned Z hZ B) (Paired.HeckeObjectClassifier.pairedHeckeObjectAligned_kernelType Z hZ M B hM)
    k (Paired.HeckeObjectClassifier.pairedHeckeObjectKernelMap_choice Z hZ hdegree M R B hM)
  let j : Paired.PELFunctor.PairedPELQuotientIso
      (R.quotient.pullback (Paired.HeckeObjectClassifier.pairedHeckeObjectClassifyingMap Z hZ hdegree M R B hM))
      (B.quotient.precompose e) := {
    source := { polarized := r.source.polarized, action := r.source.action }
    target := { polarized := r.target.polarized, action := r.target.action }
    forward_square := r.forward_square }
  exact j.trans (B.quotient.precomposeIso e)

include hZ hdegree in
omit [NumberField K] [CharZero K] in
theorem NoetherianPairedHeckeSource.PairedHeckeSource.classifying_surjective (X : Over (Spec (.of K))) :
    Function.Surjective (fun f : X ⟶ AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter =>
      TypedPairedPEL.TypedPairedPELClasses.pullback M f R.classOf) := by
  rintro ⟨q, hq⟩
  induction q using Quotient.inductionOn with
  | h B =>
    refine ⟨Paired.HeckeObjectClassifier.pairedHeckeObjectClassifyingMap Z hZ hdegree M R B hq, ?_⟩
    apply Subtype.ext
    exact Quotient.sound ⟨HeckePairClassSurjectivity.pairedHeckeObjectRecoveryIso Z hZ hdegree M R B hq⟩

def NoetherianPairedHeckeSource.PairedHeckeSource.classifying :
    uliftYoneda.{1}.obj (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter) ⟶
      TypedPairedPEL.typedPairedPELModuliFunctor P iota N n M :=
  uliftYonedaEquiv.symm R.classOf

omit [NumberField K] [CharZero K] in
theorem NoetherianPairedHeckeSource.PairedHeckeSource.classifying_apply (X : Over (Spec (.of K)))
    (f : X ⟶ AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter) :
    (R.classifying Z M).app (.op X) (ULift.up f) =
      TypedPairedPEL.TypedPairedPELClasses.pullback M f R.classOf := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
