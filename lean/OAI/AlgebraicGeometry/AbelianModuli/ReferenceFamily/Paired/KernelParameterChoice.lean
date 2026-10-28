import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TotalParameters
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ParameterSubgroupConditionReflection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.EtaleKernelModels
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalFunctionPairedKernels
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PairingFibers
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.UniversalFunctions

/-! # Kernel Parameter Choice -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.KernelParameterChoice

noncomputable section

/-! A paired quotient of the actual universal family's pullback
recovers its original finite subgroup choice, stable under every
integral coefficient and self-annihilating for its original pairing.
The parameter test scheme is unrestricted. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}

def pairedPELKernelChoice
    {T : Over (Spec (.of K))} {A B : PEL.Objects.PELObject P iota N T}
    (f : PELQuotients.PairedPELQuotient A B n)
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (hM : (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom).HasModuleType M) :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice A.polarized.abelian.scheme n M (Over.mk (𝟙 T.left)) := by
  let : Etale f.forward.isogeny.hom.left := f.forward.etale
  refine {
    subgroup := AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom
    killed := ?_
    moduleType := hM
    geometric := ⟨ReferenceFamily.Finite.EtaleKernelModels.finiteFlatMorphismKernelModel f.forward.isogeny.hom⟩ }
  intro X t x hx
  change x ≫ f.forward.isogeny.hom = 1 at hx
  calc
    x ^ n = x ≫ (𝟙 A.polarized.abelian.scheme) ^ n := by
      rw [MonObj.comp_pow, Category.comp_id]
    _ = x ≫ (f.forward.isogeny.hom ≫ f.reverse.isogeny.hom) := by rw [f.forward_reverse]
    _ = 1 := by rw [← Category.assoc, hx, MonObj.one_comp]

variable {T : Over (Spec (.of K))} (A : PEL.Objects.PELObject P iota N T) (Q : Over T.left)
    (B : PEL.Objects.PELObject P iota N (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter T Q))
    (f : PELQuotients.PairedPELQuotient (A.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T Q)) B n)
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (hM : (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom).HasModuleType M)

def pairedKernelParameterChoice : AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice A.polarized.abelian.scheme n M Q :=
  ParameterSubgroupConditionReflection.subgroupChoiceFromParameter (Grp.mk A.polarized.abelian.scheme) Q n M (pairedPELKernelChoice f M hM)

omit [NumberField K] in
theorem pairedKernelParameterChoice_overParameter :
    AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.polarized.abelian.scheme) Q
      (pairedKernelParameterChoice A Q B f M hM).subgroup = AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom :=
  Relative.SubgroupFromParameter.relativeSubgroupFromParameter_overParameter (Grp.mk A.polarized.abelian.scheme) Q _

omit [NumberField K] in
theorem pairedKernelParameterChoice_stable (a : NumberField.RingOfIntegers E) :
    AbelianScheme.IsogenyQuotient.Action.Construction.RelativeSubgroupStable (pairedKernelParameterChoice A Q B f M hM).subgroup (A.action.map a) := by
  apply ParameterSubgroupConditionReflection.relativeSubgroupFromParameter_stable (Grp.mk A.polarized.abelian.scheme) Q
    (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom) (Grp.homMk (A.action.map a))
  intro X t x hx
  change (x ≫ (A.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T Q)).action.map a) ≫ f.forward.isogeny.hom = 1
  change x ≫ f.forward.isogeny.hom = 1 at hx
  rw [Category.assoc, ← f.forward.action a, ← Category.assoc, hx, MonObj.one_comp]

omit [NumberField K] in
theorem pairedKernelParameterChoice_self_annihilating [IsLocallyNoetherian T.left]
    (hn : 0 < n) (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2)) :
    let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.polarized.abelian.scheme n)
      (pairedKernelParameterChoice A Q B f M hM).subgroup
    (AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual
      A.polarized.polarization n hn).relativeAnnihilator H = H := by
  let hA := AbelianScheme.IsogenyQuotient.Noetherian.UniversalFunctions.Construction.noetherianAbelian_hasUniversalGlobalFunctions A.polarized.abelian
  let hDA := AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA
  have hp := UniversalFunctionPairedKernels.universalFunction_pairedPELQuotient_forward_kernel_self_annihilating f
    (hA.pullback Q.hom) hn hdegree
  change (AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing
      (A.polarized.abelian.pullback Q.hom) (A.polarized.dual.pullback Q.hom)
      (A.polarized.polarization.pullback Q.hom) (hDA.pullback Q.hom) n hn).relativeAnnihilator
        (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback
          (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion (A.polarized.abelian.pullback Q.hom).scheme n)
          (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom)) = _ at hp
  rw [AbelianScheme.IsogenyQuotient.UniversalFunction.PairingFibers.Construction.universalFunctionNativePolarizationPairing_baseChange A.polarized.dual hDA
    A.polarized.polarization n hn Q.hom,
    UniversalFunctionPairedKernels.universalFunctionNativePolarizationPairing_eq_noetherian A.polarized.abelian
      A.polarized.dual A.polarized.polarization hDA n hn] at hp
  apply (ParameterSubgroupConditionReflection.nativeTorsionSubgroupOverParameter_self_annihilating_iff
    (Grp.mk A.polarized.abelian.scheme) Q n (pairedKernelParameterChoice A Q B f M hM).subgroup
    (AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual
      A.polarized.polarization n hn)).mp
  rw [pairedKernelParameterChoice_overParameter]
  exact hp

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.KernelParameterChoice
