import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HeckePairRecovery
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELSourceTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RigidPairedKernelClasses

/-! # Hecke Fixed Source Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Over a fixed source point, the actual universal paired quotient
recovers exactly the pulled-back subgroup choice. Full-level rigidity
therefore makes the resulting paired-class map injective. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} [IsLocallyNoetherian T.left]
    {A : PEL.Objects.PELObject P iota N T} {hn : 0 < n}
    {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (R : NoetherianPairedHeckeSource.PairedHeckeSource A n hn M) {Q : Over T.left}

def NoetherianPairedHeckeSource.PairedHeckeSource.pairAtParameter (k : Q ⟶ R.parameter) :
    Paired.PELQuotients.PairedPELQuotient (A.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T Q))
      (R.target.pullback (PEL.ParameterPullbackComparison.parameterTotalMap k)) n :=
  (R.quotient.pullback (PEL.ParameterPullbackComparison.parameterTotalMap k)).precompose (PEL.ParameterPullbackComparison.pelParameterPullbackIso A k).symm

omit [NumberField K] [CharZero K] in
theorem NoetherianPairedHeckeSource.PairedHeckeSource.pairAtParameter_kernelType (k : Q ⟶ R.parameter) :
    (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (R.pairAtParameter k).forward.isogeny.hom).HasModuleType M :=
  (((R.quotient.pullback (PEL.ParameterPullbackComparison.parameterTotalMap k)).precomposeIso
    (PEL.ParameterPullbackComparison.pelParameterPullbackIso A k).symm).kernel_moduleType_iff M).mpr
      (R.quotient.kernel_moduleType_pullback M R.kernelType (PEL.ParameterPullbackComparison.parameterTotalMap k))

omit [NumberField K] [CharZero K] in
theorem NoetherianPairedHeckeSource.PairedHeckeSource.pairAtParameter_kernel
    (k : Q ⟶ R.parameter) (X : Over Q.left)
    (x : X ⟶ (A.polarized.abelian.pullback Q.hom).scheme) :
    x ≫ (R.pairAtParameter k).forward.isogeny.hom = 1 ↔
      A.polarized.abelian.baseChangePointsMulEquiv Q.hom X x ∈
        (R.subgroup.subgroup.baseChange k).points ((Over.map Q.hom).obj X) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint Q X) := by
  let e := (PEL.ParameterPullbackComparison.pelParameterPullbackIso A k).polarized.abelian
  change x ≫ (e.inv ≫ (R.quotient.forward.isogeny.pullback k.left).hom) = 1 ↔ _
  erw [← Category.assoc, HeckePairRecovery.isogeny_pullback_kernel_iff]
  erw [R.kernel ((Over.map k.left).obj X)
    ((A.polarized.abelian.pullback R.parameter.hom).baseChangePointsMulEquiv k.left X (x ≫ e.inv))]
  erw [PEL.ParameterPullbackComparison.pelParameterPullbackIso_subgroup_membership A k R.subgroup.subgroup X (x ≫ e.inv)]
  change A.polarized.abelian.baseChangePointsMulEquiv Q.hom X ((x ≫ e.inv) ≫ e.hom) ∈ _ ↔ _
  erw [Category.assoc, e.inv_hom_id, Category.comp_id]

omit [NumberField K] [CharZero K] in
theorem NoetherianPairedHeckeSource.PairedHeckeSource.pairAtParameter_choice (k : Q ⟶ R.parameter) :
    Paired.KernelParameterChoice.pairedKernelParameterChoice A Q (R.target.pullback (PEL.ParameterPullbackComparison.parameterTotalMap k))
      (R.pairAtParameter k) M (R.pairAtParameter_kernelType k) = R.subgroup.baseChange k := by
  apply AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice.ext
  apply AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.relativeSubgroupOverParameter_injective
    (Grp.mk A.polarized.abelian.scheme) Q
  rw [Paired.KernelParameterChoice.pairedKernelParameterChoice_overParameter]
  ext X t x
  exact R.pairAtParameter_kernel k X x

def NoetherianPairedHeckeSource.PairedHeckeSource.objectAtParameter (k : Q ⟶ R.parameter) :
    Paired.PELFunctor.PairedPELObject P iota N n (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter T Q) where
  source := A.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T Q)
  target := R.target.pullback (PEL.ParameterPullbackComparison.parameterTotalMap k)
  quotient := R.pairAtParameter k

def NoetherianPairedHeckeSource.PairedHeckeSource.classAtParameter (k : Q ⟶ R.parameter) :
    TypedPairedPEL.TypedPairedPELClasses P iota N n M (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter T Q) :=
  ⟨(R.objectAtParameter k).classOf, R.pairAtParameter_kernelType k⟩

theorem NoetherianPairedHeckeSource.PairedHeckeSource.classAtParameter_injective [LocallyOfFiniteType T.hom]
    (hN : 3 ≤ N) (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2)) :
    Function.Injective (R.classAtParameter (Q := Q)) := by
  intro k l h
  obtain ⟨e⟩ : Nonempty (Paired.PELFunctor.PairedPELQuotientIso (R.pairAtParameter k) (R.pairAtParameter l)) :=
    Quotient.exact (congrArg Subtype.val h)
  have hF := RigidPairedKernelClasses.pairedKernelParameterChoice_eq_of_iso A hN Q e M
    (R.pairAtParameter_kernelType k) (R.pairAtParameter_kernelType l)
  obtain ⟨a, _, ha⟩ := R.classifiesKernel hdegree Q
    (R.target.pullback (PEL.ParameterPullbackComparison.parameterTotalMap k)) (R.pairAtParameter k) (R.pairAtParameter_kernelType k)
  apply (ha k (R.pairAtParameter_choice k).symm).trans
  exact (ha l ((R.pairAtParameter_choice l).symm.trans hF.symm)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
