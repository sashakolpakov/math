import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.UniversalTarget
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PairingFibers
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.QuotientFineTarget

/-! # Target -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Target.Construction

noncomputable section

/-! The actual universal quotient and fine target over arbitrary bases
with universal global functions of the original PEL family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {d N : ℕ} {D : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))}

variable [CharZero K]

set_option backward.isDefEq.respectTransparency false in
theorem universalFunction_universal_fine_target
    (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T) (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A.polarized.abelian.scheme) (n : ℕ) (hn : 0 < n)
    (M : Fin d → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)] [∀ i, Finite (M i)]
    (p r : Fin d → (A.polarized.abelian.scheme ⟶ A.polarized.abelian.scheme))
    [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (r i)]
    (ep : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (r i))
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.left).X))
    (hu : Universal.Isotropic.Construction.UniversalIsotropicNativeFamily A n M p r
      (PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A.polarized.abelian A.polarized.dual A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) n hn) ep)
    (hc : Nat.Coprime n ((∏ j, D.polarizationType j) ^ 2))
    (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel D iota N) (hZ : Z.IsFine) :
    Noetherian.UniversalTarget.Construction.UniversalFinePELFamily A n M p r ep Z := by
  obtain ⟨Q, hQf, hQe, repr, R, B, f, g, σ, level,
    hf, hg, hfg, _hgf, hσ, _hranks, hlevel, hker, _hUP, hiso⟩ := hu
  have : Etale Q.hom := hQe
  have : Etale f.hom.left := hf
  have : IsMonHom g := hg
  let AC := PELBaseChange.Construction.pelObjectPullback A (TotalParameters.Construction.totalParameterSource T Q)
  have hAC : GlobalFunctions.Construction.HasUniversalGlobalFunctions AC.polarized.abelian.scheme := hA.pullback Q.hom
  have hDC := (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA).pullback Q.hom
  have hk : ∀ (U : Over (TotalParameters.Construction.totalParameter T Q).left) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom), x ^ n = 1 := by
    intro U x
    apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f.hom)).mp
    rw [MonObj.pow_comp, MonObj.one_comp]
    exact FppfPowerComplement.Construction.powerComplement_kernel_torsion g f.hom n hfg U (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f.hom)
      (by rw [Category.assoc, Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp, MonObj.comp_one])
  let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion AC.polarized.abelian.scheme n)
    (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom)
  have hi : (PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing AC.polarized.abelian AC.polarized.dual
      AC.polarized.polarization hDC n hn).relativeAnnihilator H = H :=
    (congrArg (fun e => e.relativeAnnihilator H)
      (PairingFibers.Construction.universalFunctionNativePolarizationPairing_baseChange A.polarized.dual (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) A.polarized.polarization n hn Q.hom)).trans hiso
  have hl := PairingFibers.Construction.universalFunctionCanonicalKernel_geometric_selfAnnihilating AC.polarized.dual hDC
    AC.polarized.polarization n hn f hi
  let target := QuotientFineTarget.Construction.universalFunctionQuotientFineTargetData AC hAC n hn f σ level (fun a => (hσ a).symm)
    hk hl hc hlevel Z hZ
  refine ⟨Q, hQf, hQe, repr, R, target, ?_⟩
  intro U a
  let t : U ⟶ Over.mk (𝟙 Q.left) := Over.homMk U.hom (Category.comp_id _)
  have he := congrArg (fun H => a ∈ H.points U t)
    (QuotientFineTarget.Construction.universalFunctionQuotientFineTargetData_kernel AC hAC n hn f σ level (fun a => (hσ a).symm)
      hk hl hc hlevel Z hZ)
  exact (iff_of_eq he).trans (hker U a)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Target.Construction
