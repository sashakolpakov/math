import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NumberFieldCountability
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.HeckeKernelClassification
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.PullbackIsoUniqueness

/-! # Rigid Paired Kernel Classes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Full level rigidity makes the original kernel classifier
independent of a paired PEL isomorphism over a fixed universal source.
The full kernel equality holds on arbitrary scheme-valued points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}

theorem RigidPairedKernelClasses.pairedPELKernel_eq_of_source_identity
    {T : Over (Spec (.of K))} {A B C : PEL.Objects.PELObject P iota N T}
    {f : Paired.PELQuotients.PairedPELQuotient A B n} {g : Paired.PELQuotients.PairedPELQuotient A C n}
    (e : Paired.PELFunctor.PairedPELQuotientIso f g)
    (he : e.source.polarized.abelian.hom = 𝟙 A.polarized.abelian.scheme) :
    AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom = AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel g.forward.isogeny.hom := by
  have hs := e.forward_square
  rw [he, Category.id_comp] at hs
  ext X t x
  change x ≫ f.forward.isogeny.hom = 1 ↔ x ≫ g.forward.isogeny.hom = 1
  constructor
  · intro hx
    rw [← hs, ← Category.assoc, hx, MonObj.one_comp]
  · intro hx
    apply (cancel_mono e.target.polarized.abelian.hom).mp
    rw [Category.assoc, hs, hx, MonObj.one_comp]

variable [NumberField K] [CharZero K]
    {T : Over (Spec (.of K))} [LocallyOfFiniteType T.hom]
    (A : PEL.Objects.PELObject P iota N T) (hN : 3 ≤ N)
    (X : Over T.left) {B C : PEL.Objects.PELObject P iota N (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter T X)}
    {f : Paired.PELQuotients.PairedPELQuotient (A.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T X)) B n}
    {g : Paired.PELQuotients.PairedPELQuotient (A.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T X)) C n}

include hN in
theorem RigidPairedKernelClasses.pairedPELKernel_eq_of_fixed_source_iso (e : Paired.PELFunctor.PairedPELQuotientIso f g) :
    AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom = AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel g.forward.isogeny.hom := by
  have : Countable K := NumberFieldCountability.numberField_countable K
  exact RigidPairedKernelClasses.pairedPELKernel_eq_of_source_identity e
    (Pure.PullbackRigidity.purePullback_abelian_eq_id T.hom A.polarized hN X.hom e.source.polarized)

include hN in
theorem RigidPairedKernelClasses.pairedKernelParameterChoice_eq_of_iso (e : Paired.PELFunctor.PairedPELQuotientIso f g)
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (hf : (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom).HasModuleType M)
    (hg : (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel g.forward.isogeny.hom).HasModuleType M) :
    Paired.KernelParameterChoice.pairedKernelParameterChoice A X B f M hf = Paired.KernelParameterChoice.pairedKernelParameterChoice A X C g M hg := by
  apply AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice.ext
  exact congrArg (Relative.SubgroupFromParameter.relativeSubgroupFromParameter (Grp.mk A.polarized.abelian.scheme) X)
    (RigidPairedKernelClasses.pairedPELKernel_eq_of_fixed_source_iso A hN X e)

include hN in
theorem NoetherianPairedHeckeSource.PairedHeckeSource.kernelClassifier_eq_of_iso
    [IsLocallyNoetherian T.left] {hn : 0 < n}
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (R : NoetherianPairedHeckeSource.PairedHeckeSource A n hn M)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (e : Paired.PELFunctor.PairedPELQuotientIso f g)
    (hf : (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom).HasModuleType M)
    (hg : (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel g.forward.isogeny.hom).HasModuleType M)
    (k l : X ⟶ R.parameter)
    (hk : R.subgroup.baseChange k = Paired.KernelParameterChoice.pairedKernelParameterChoice A X B f M hf)
    (hl : R.subgroup.baseChange l = Paired.KernelParameterChoice.pairedKernelParameterChoice A X C g M hg) : k = l := by
  obtain ⟨a, _, ha⟩ := R.classifiesKernel hdegree X B f hf
  have hF := RigidPairedKernelClasses.pairedKernelParameterChoice_eq_of_iso A hN X e M hf hg
  exact (ha k hk).trans (ha l (hl.trans hF.symm)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
