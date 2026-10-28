import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.HeckeKernelClassification
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELSourceTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.SourceParameterRelabel

/-! # Hecke Object Classifier -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.HeckeObjectClassifier

noncomputable section

/-! Construct the actual map from any typed paired PEL object to
the finite etale Hecke parameter. The source classifier and full kernel
choice determine the map; descent to isomorphism classes is separate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (Z : Models.FinePELModel P iota N) (hZ : Z.IsFine) [IsLocallyNoetherian Z.space.left]
    {hn : 0 < n} (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (R : NoetherianPairedHeckeSource.PairedHeckeSource Z.universal n hn M)
    {X : Over (Spec (.of K))} (B : PELFunctor.PairedPELObject P iota N n X)
    (hM : (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel B.quotient.forward.isogeny.hom).HasModuleType M)

def pairedHeckeObjectSource : X ⟶ Z.space := AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap Z hZ B.source

def pairedHeckeObjectSourceIso :
    PEL.Objects.PELIso (Z.universal.pullback (pairedHeckeObjectSource Z hZ B)) B.source :=
  (AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingIso Z hZ B.source).toPELIso.symm

def pairedHeckeObjectAligned :
    PELQuotients.PairedPELQuotient
      (Z.universal.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space
        (Over.mk (pairedHeckeObjectSource Z hZ B).left)))
      (B.target.overSourceParameter (pairedHeckeObjectSource Z hZ B)) n :=
  PEL.SourceParameterRelabel.pairedPELOverSourceParameter (pairedHeckeObjectSource Z hZ B)
    (B.quotient.precompose (pairedHeckeObjectSourceIso Z hZ B))

include hM in
omit [NumberField K] [CharZero K] [IsLocallyNoetherian Z.space.left]
  [Module (ZMod n) M] [Finite M] in
theorem pairedHeckeObjectAligned_kernelType :
    (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (pairedHeckeObjectAligned Z hZ B).forward.isogeny.hom).HasModuleType M :=
  ((B.quotient.precomposeIso (pairedHeckeObjectSourceIso Z hZ B)).kernel_moduleType_iff M).mpr hM

def pairedHeckeObjectKernelChoice :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice Z.universal.polarized.abelian.scheme n M
      (Over.mk (pairedHeckeObjectSource Z hZ B).left) :=
  KernelParameterChoice.pairedKernelParameterChoice Z.universal (Over.mk (pairedHeckeObjectSource Z hZ B).left)
    (B.target.overSourceParameter (pairedHeckeObjectSource Z hZ B))
    (pairedHeckeObjectAligned Z hZ B) M (pairedHeckeObjectAligned_kernelType Z hZ M B hM)

include hdegree in
omit [NumberField K] [CharZero K] in
theorem pairedHeckeObjectKernel_classified :
    ∃! k : Over.mk (pairedHeckeObjectSource Z hZ B).left ⟶ R.parameter,
      R.subgroup.baseChange k = pairedHeckeObjectKernelChoice Z hZ M B hM :=
  R.classifiesKernel hdegree (Over.mk (pairedHeckeObjectSource Z hZ B).left)
    (B.target.overSourceParameter (pairedHeckeObjectSource Z hZ B))
    (pairedHeckeObjectAligned Z hZ B) (pairedHeckeObjectAligned_kernelType Z hZ M B hM)

def pairedHeckeObjectKernelMap : Over.mk (pairedHeckeObjectSource Z hZ B).left ⟶ R.parameter :=
  (pairedHeckeObjectKernel_classified Z hZ hdegree M R B hM).choose

omit [NumberField K] [CharZero K] in
theorem pairedHeckeObjectKernelMap_choice :
    R.subgroup.baseChange (pairedHeckeObjectKernelMap Z hZ hdegree M R B hM) =
      pairedHeckeObjectKernelChoice Z hZ M B hM :=
  (pairedHeckeObjectKernel_classified Z hZ hdegree M R B hM).choose_spec.1

def pairedHeckeObjectClassifyingMap : X ⟶ AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter :=
  ((AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterFiberLiftEquiv Z.space R.parameter X (pairedHeckeObjectSource Z hZ B)).symm
    (pairedHeckeObjectKernelMap Z hZ hdegree M R B hM)).val

omit [NumberField K] [CharZero K] in
theorem pairedHeckeObjectClassifyingMap_source :
    pairedHeckeObjectClassifyingMap Z hZ hdegree M R B hM ≫
      AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space R.parameter = pairedHeckeObjectSource Z hZ B :=
  ((AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterFiberLiftEquiv Z.space R.parameter X (pairedHeckeObjectSource Z hZ B)).symm
    (pairedHeckeObjectKernelMap Z hZ hdegree M R B hM)).property

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.HeckeObjectClassifier
