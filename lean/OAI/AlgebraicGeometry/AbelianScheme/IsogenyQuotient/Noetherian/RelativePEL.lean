import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PairingFibers
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Isotropic

/-! # Relative PEL -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.RelativePEL.Construction

noncomputable section

/-! Construct the full PEL quotient of an individual relative subgroup.
Its parameter need not be the universal subgroup parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {d N : ℕ} {D : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))}

def RelativePELQuotient (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T) (Q : Over T.left)
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.polarized.abelian.scheme Q) (n : ℕ) : Prop :=
  ∃ B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N (TotalParameters.Construction.totalParameter T Q),
    ∃ f : Intrinsic.PELBaseChange.Construction.NativePELQuotient (PELBaseChange.Construction.pelObjectPullback A (TotalParameters.Construction.totalParameterSource T Q)) B n,
      ∀ (U : Over (TotalParameters.Construction.totalParameter T Q).left)
        (a : U ⟶ (A.polarized.abelian.pullback Q.hom).scheme),
        a ≫ f.isogeny.hom = 1 ↔ A.polarized.abelian.baseChangePointsMulEquiv Q.hom U a ∈
          F.points ((Over.map Q.hom).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint Q U)

set_option backward.isDefEq.respectTransparency false in
theorem noetherian_relative_pel_quotient_from_FiniteDescent
    [CharZero K] [IsLocallyNoetherian T.left]
    (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T) (Q : Over T.left) [IsLocallyNoetherian Q.left]
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.polarized.abelian.scheme Q) (R : F.Model)
    (n : ℕ) (hn : 0 < n) (hkilled : F.KilledBy n)
    (hcop : Nat.Coprime n N) (hdegree : Nat.Coprime n ((∏ i, D.polarizationType i) ^ 2))
    (hstable : ∀ a, Action.Construction.RelativeSubgroupStable F (A.action.map a))
    (hisotropic :
      let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A.polarized.abelian.scheme n) F
      (PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual
        A.polarized.polarization n hn).relativeAnnihilator H = H)
    (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0}) : RelativePELQuotient A Q F n := by
  have : IsLocallyNoetherian (TotalParameters.Construction.totalParameter T Q).left := inferInstanceAs (IsLocallyNoetherian Q.left)
  have htor := Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A.polarized.abelian.scheme) T.hom n hn Torsion.Construction.verified_TorsionQuotientInput
  obtain ⟨B, f, g, hf, hg, hfg, hgf, hker, hUP⟩ :=
    Intrinsic.RelativeQuotient.Construction.native_relative_quotient_from_TorsionQuotient_FiniteDescent A.polarized.abelian Q F R n hkilled htor.2 h_FiniteDescent
  obtain ⟨σ, hσ, _⟩ := Intrinsic.Action.Construction.native_quotient_integral_action A.polarized.abelian Q F R B f hker hUP A.action hstable
  have : Etale f.hom.left := hf
  have : IsMonHom g := hg
  let AC := PELBaseChange.Construction.pelObjectPullback A (TotalParameters.Construction.totalParameterSource T Q)
  let level := Markings.Construction.transportFullLevel AC.polarized.abelian B f.hom g n N hcop hfg hgf AC.polarized.level
  have hk : ∀ (U : Over (TotalParameters.Construction.totalParameter T Q).left) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom), x ^ n = 1 := by
    intro U x
    apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f.hom)).mp
    rw [MonObj.pow_comp, MonObj.one_comp]
    exact FppfPowerComplement.Construction.powerComplement_kernel_torsion g f.hom n hfg U (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f.hom)
      (by rw [Category.assoc, Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp, MonObj.comp_one])
  let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion AC.polarized.abelian.scheme n)
    (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom)
  have hi : (PolarizationAdapter.Construction.noetherianNativePolarizationPairing AC.polarized.abelian AC.polarized.dual
      AC.polarized.polarization n hn).relativeAnnihilator H = H :=
    (congrArg (fun e => e.relativeAnnihilator H)
      (PairingFibers.Construction.noetherianNativePolarizationPairing_baseChange A.polarized.dual A.polarized.polarization n hn Q.hom)).trans
        (Intrinsic.Isotropy.Construction.nativeQuotient_kernel_self_annihilating A.polarized.abelian Q F R f hker n _ hisotropic)
  have hl := PairingFibers.Construction.noetherianCanonicalKernel_geometric_selfAnnihilating AC.polarized.dual
    AC.polarized.polarization n hn f hi
  let BPEL := PEL.Construction.noetherianQuotientPEL AC n hn f σ level (fun a => (hσ a).symm) hk hl hdegree
  let fq : Intrinsic.PELBaseChange.Construction.NativePELQuotient AC BPEL n := {
    isogeny := f
    etale := hf
    polarization := PEL.Construction.noetherianQuotientPEL_polarization AC n hn f σ level (fun a => (hσ a).symm) hk hl hdegree
    action := hσ
    marking := fun U c => (Markings.Construction.transportFullLevel_apply AC.polarized.abelian B f.hom g n N hcop hfg hgf
      AC.polarized.level U c).symm }
  exact ⟨BPEL, fq, Intrinsic.KernelPoints.Construction.nativeQuotient_kernel_membership A.polarized.abelian Q F R f hker⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.RelativePEL.Construction
