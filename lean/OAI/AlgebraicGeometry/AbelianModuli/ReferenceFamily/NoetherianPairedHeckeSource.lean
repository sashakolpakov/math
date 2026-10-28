import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NoetherianHeckeSource
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELQuotientKernelType
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TypedPairedPEL

/-! # Noetherian Paired Hecke Source -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NoetherianPairedHeckeSource

noncomputable section

/-! The finite etale parameter of stable self-annihilating subgroups
carries actual paired PEL isogenies of precisely the chosen kernel
type. Its target is constructed from its universal quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} [IsLocallyNoetherian T.left]

structure PairedHeckeSource (A : PEL.Objects.PELObject P iota N T)
    (n : ℕ) (hn : 0 < n) (M : Type) [AddCommGroup M]
    [Module (ZMod n) M] [Finite M] where
  parameter : Over T.left
  subgroup : AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice A.polarized.abelian.scheme n M parameter
  finite : IsFinite parameter.hom
  etale : Etale parameter.hom
  stable : ∀ a, SubgroupStability.RelativeSubgroupStable subgroup.subgroup (A.action.map a)
  selfAnn :
    let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback
      (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.polarized.abelian.scheme n) subgroup.subgroup
    (AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual
      A.polarized.polarization n hn).relativeAnnihilator H = H
  classify : ∀ (X : Over T.left) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice A.polarized.abelian.scheme n M X),
    ((∀ a, SubgroupStability.RelativeSubgroupStable F.subgroup (A.action.map a)) ∧
      (let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback
        (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.polarized.abelian.scheme n) F.subgroup
       (AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual
         A.polarized.polarization n hn).relativeAnnihilator H = H)) ↔
      ∃! f : X ⟶ parameter, subgroup.baseChange f = F
  target : PEL.Objects.PELObject P iota N (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter T parameter)
  quotient : Paired.PELQuotients.PairedPELQuotient (A.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T parameter)) target n
  kernel : ∀ (X : Over parameter.left)
    (x : X ⟶ (A.polarized.abelian.pullback parameter.hom).scheme),
    x ≫ quotient.forward.isogeny.hom = 1 ↔
      A.polarized.abelian.baseChangePointsMulEquiv parameter.hom X x ∈
        subgroup.subgroup.points ((Over.map parameter.hom).obj X) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint parameter X)
  kernelType : (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel quotient.forward.isogeny.hom).HasModuleType M

theorem exists_noetherian_paired_hecke_source
    (A : PEL.Objects.PELObject P iota N T) (n : ℕ) (hn : 0 < n)
    (hN : Nat.Coprime n N) (hmod : Nat.ModEq N n 1)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M] :
    Nonempty (PairedHeckeSource A n hn M) := by
  obtain ⟨Q, U, hQf, hQe, hs, hl, hquot, hc⟩ :=
    NoetherianHeckeSource.exists_noetherian_pel_hecke_source A n hn hN hdegree M
  let : Etale Q.hom := hQe
  let : IsLocallyNoetherian Q.left := LocallyOfFiniteType.isLocallyNoetherian Q.hom
  let : IsLocallyNoetherian (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter T Q).left :=
    inferInstanceAs (IsLocallyNoetherian Q.left)
  obtain ⟨f, hf⟩ := Paired.PELQuotients.exists_paired_pel_quotient hquot.quotient hn hmod
    (Relative.PELQuotientKernelType.relativePELQuotient_kernel_killed hquot U.killed)
  refine ⟨{
    parameter := Q
    subgroup := U
    finite := hQf
    etale := hQe
    stable := hs
    selfAnn := hl
    classify := hc
    target := hquot.object
    quotient := f
    kernel := ?_
    kernelType := ?_ }⟩
  · intro X x
    rw [hf]
    exact hquot.kernel X x
  · rw [hf]
    exact Relative.PELQuotientKernelType.relativePELQuotient_kernel_moduleType hquot M U.moduleType

def PairedHeckeSource.pairedObject {A : PEL.Objects.PELObject P iota N T}
    {hn : 0 < n} {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (Q : PairedHeckeSource A n hn M) : Paired.PELFunctor.PairedPELObject P iota N n (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter T Q.parameter) where
  source := A.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T Q.parameter)
  target := Q.target
  quotient := Q.quotient

def PairedHeckeSource.classOf {A : PEL.Objects.PELObject P iota N T}
    {hn : 0 < n} {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (Q : PairedHeckeSource A n hn M) :
    TypedPairedPEL.TypedPairedPELClasses P iota N n M (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter T Q.parameter) :=
  ⟨Q.pairedObject.classOf, Q.kernelType⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NoetherianPairedHeckeSource
