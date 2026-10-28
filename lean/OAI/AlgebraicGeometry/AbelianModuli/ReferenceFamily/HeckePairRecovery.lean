import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.HeckeKernelClassification
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.ParameterPullbackComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELQuotientComparison

/-! # Hecke Pair Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The unique original-kernel classifier recovers the entire paired
PEL quotient as the actual pullback of the universal pair. The source
comparison is the canonical PEL base-change comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem HeckePairRecovery.isogeny_pullback_kernel_iff
    {S S' : Scheme.{0}} {g h : ℕ}
    {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (f : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (b : S' ⟶ S)
    (X : Over S') (x : X ⟶ (A.pullback b).scheme) :
    x ≫ (f.pullback b).hom = 1 ↔ A.baseChangePointsMulEquiv b X x ≫ f.hom = 1 := by
  have hn := HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map f.hom b X x
  constructor
  · intro hx
    exact hn.symm.trans ((congrArg (B.baseChangePointsMulEquiv b X) hx).trans
      (B.baseChangePointsMulEquiv b X).map_one)
  · intro hx
    apply (B.baseChangePointsMulEquiv b X).injective
    exact hn.trans (hx.trans (B.baseChangePointsMulEquiv b X).map_one.symm)

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} [IsLocallyNoetherian T.left]
    {A : PEL.Objects.PELObject P iota N T} {hn : 0 < n}
    {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (R : NoetherianPairedHeckeSource.PairedHeckeSource A n hn M)
    (Q : Over T.left) (B : PEL.Objects.PELObject P iota N (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter T Q))
    (f : Paired.PELQuotients.PairedPELQuotient (A.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T Q)) B n)
    (hM : (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom).HasModuleType M)

omit [NumberField K] [CharZero K] in
theorem NoetherianPairedHeckeSource.PairedHeckeSource.classifier_sameKernel
    (k : Q ⟶ R.parameter)
    (hk : R.subgroup.baseChange k = Paired.KernelParameterChoice.pairedKernelParameterChoice A Q B f M hM)
    (X : Over Q.left)
    (x : X ⟶ ((A.polarized.abelian.pullback R.parameter.hom).pullback k.left).scheme) :
    x ≫ (R.quotient.pullback (PEL.ParameterPullbackComparison.parameterTotalMap k)).forward.isogeny.hom = 1 ↔
      (x ≫ (PEL.ParameterPullbackComparison.pelParameterPullbackIso A k).polarized.abelian.hom) ≫ f.forward.isogeny.hom = 1 := by
  erw [HeckePairRecovery.isogeny_pullback_kernel_iff R.quotient.forward.isogeny k.left X x]
  erw [R.kernel ((Over.map k.left).obj X)
    ((A.polarized.abelian.pullback R.parameter.hom).baseChangePointsMulEquiv k.left X x)]
  erw [PEL.ParameterPullbackComparison.pelParameterPullbackIso_subgroup_membership A k R.subgroup.subgroup X x]
  have hsub : R.subgroup.subgroup.baseChange k =
      (Paired.KernelParameterChoice.pairedKernelParameterChoice A Q B f M hM).subgroup :=
    congrArg AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice.subgroup hk
  rw [hsub]
  have h := congrArg (fun H =>
    (x ≫ (PEL.ParameterPullbackComparison.pelParameterPullbackIso A k).polarized.abelian.hom) ∈
      H.points X (Relative.SubgroupFromParameter.terminalParameterPoint X))
    (Paired.KernelParameterChoice.pairedKernelParameterChoice_overParameter A Q B f M hM)
  exact iff_of_eq h

def NoetherianPairedHeckeSource.PairedHeckeSource.pairIsoOfClassifier
    (k : Q ⟶ R.parameter)
    (hk : R.subgroup.baseChange k = Paired.KernelParameterChoice.pairedKernelParameterChoice A Q B f M hM) :
    Paired.PELFunctor.PairedPELQuotientIso (R.quotient.pullback (PEL.ParameterPullbackComparison.parameterTotalMap k)) f :=
  Paired.PELQuotientComparison.pairedPELQuotientIsoOfKernel (R.quotient.pullback (PEL.ParameterPullbackComparison.parameterTotalMap k)) f
    (((AbelianScheme.IsogenyQuotient.Noetherian.UniversalFunctions.Construction.noetherianAbelian_hasUniversalGlobalFunctions A.polarized.abelian).pullback
      R.parameter.hom).pullback k.left)
    (PEL.ParameterPullbackComparison.pelParameterPullbackIso A k) (R.classifier_sameKernel Q B f hM k hk)

omit [NumberField K] [CharZero K] in
theorem NoetherianPairedHeckeSource.PairedHeckeSource.exists_pair_pullback
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2)) :
    ∃! k : Q ⟶ R.parameter,
      R.subgroup.baseChange k = Paired.KernelParameterChoice.pairedKernelParameterChoice A Q B f M hM ∧
        Nonempty (Paired.PELFunctor.PairedPELQuotientIso (R.quotient.pullback (PEL.ParameterPullbackComparison.parameterTotalMap k)) f) := by
  obtain ⟨k, hk, hu⟩ := R.classifiesKernel hdegree Q B f hM
  exact ⟨k, ⟨hk, ⟨R.pairIsoOfClassifier Q B f hM k hk⟩⟩, fun l hl => hu l hl.1⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
