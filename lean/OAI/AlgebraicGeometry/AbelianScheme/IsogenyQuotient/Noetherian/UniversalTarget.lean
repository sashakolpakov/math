import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PairingFibers
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Isotropic

/-! # Universal Target -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.UniversalTarget.Construction

noncomputable section

/-! The finite etale scheme of native subgroup choices carries one
actual fine-moduli target, with its full quotient kernel on every test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {d N : ℕ} {D : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))}

def UniversalFinePELFamily
    (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T) (n : ℕ)
    (M : Fin d → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)] [∀ i, Finite (M i)]
    (p r : Fin d → (A.polarized.abelian.scheme ⟶ A.polarized.abelian.scheme))
    [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (r i)]
    (ep : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (r i))
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.left).X)) (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel D iota N) : Prop :=
    ∃ Q : Over T.left, IsFinite Q.hom ∧ Etale Q.hom ∧
      ∃ repr : (Parameter.Products.Construction.blockTupleFunctor d (fun i =>
        SubgroupFunctor.Construction.supportedSubgroupFunctor A.polarized.abelian.scheme n (M i) (p i))).RepresentableBy Q,
      let F := ChoiceKernel.Construction.choiceFullKernel n d M p r ep (Universal.Choices.Construction.universalBlockChoice n d M p repr)
      ∃ R : F.Model,
      let AC := PELBaseChange.Construction.pelObjectPullback A (TotalParameters.Construction.totalParameterSource T Q)
      ∃ target : IntrinsicFineTargetData.Construction.NativeFinePELTarget AC n Z,
        ∀ (U : Over (TotalParameters.Construction.totalParameter T Q).left) (a : U ⟶ AC.polarized.abelian.scheme),
          a ≫ target.isogeny.hom = 1 ↔ ∃! z : U ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
            z ≫ Intrinsic.Stability.Construction.nativeSubgroupInclusion A.polarized.abelian Q F R = a

variable [CharZero K] [IsLocallyNoetherian T.left]

set_option backward.isDefEq.respectTransparency false in
theorem noetherian_universal_fine_target
    (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T) (n : ℕ) (hn : 0 < n)
    (M : Fin d → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)] [∀ i, Finite (M i)]
    (p r : Fin d → (A.polarized.abelian.scheme ⟶ A.polarized.abelian.scheme))
    [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (r i)]
    (ep : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (r i))
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.left).X))
    (hu : Universal.Isotropic.Construction.UniversalIsotropicNativeFamily A n M p r
      (PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual A.polarized.polarization n hn) ep)
    (hc : Nat.Coprime n ((∏ j, D.polarizationType j) ^ 2))
    (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel D iota N) (hZ : Z.IsFine) :
    UniversalFinePELFamily A n M p r ep Z := by
  obtain ⟨Q, hQf, hQe, repr, R, B, f, g, σ, level,
    hf, hg, hfg, _hgf, hσ, _hranks, hlevel, hker, _hUP, hiso⟩ := hu
  have : Etale Q.hom := hQe
  have : IsLocallyNoetherian Q.left := LocallyOfFiniteType.isLocallyNoetherian Q.hom
  have : IsLocallyNoetherian (TotalParameters.Construction.totalParameter T Q).left := inferInstanceAs (IsLocallyNoetherian Q.left)
  have : Etale f.hom.left := hf
  have : IsMonHom g := hg
  let AC := PELBaseChange.Construction.pelObjectPullback A (TotalParameters.Construction.totalParameterSource T Q)
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
      (PairingFibers.Construction.noetherianNativePolarizationPairing_baseChange A.polarized.dual A.polarized.polarization n hn Q.hom)).trans hiso
  have hl := PairingFibers.Construction.noetherianCanonicalKernel_geometric_selfAnnihilating AC.polarized.dual
    AC.polarized.polarization n hn f hi
  let target := IntrinsicFineTargetData.Construction.noetherianQuotientFineTargetData AC n hn f σ level (fun a => (hσ a).symm)
    hk hl hc hlevel Z hZ
  refine ⟨Q, hQf, hQe, repr, R, target, ?_⟩
  intro U a
  let t : U ⟶ Over.mk (𝟙 Q.left) := Over.homMk U.hom (Category.comp_id _)
  have he := congrArg (fun H => a ∈ H.points U t)
    (IntrinsicFineTargetData.Construction.noetherianQuotientFineTargetData_kernel AC n hn f σ level (fun a => (hσ a).symm)
      hk hl hc hlevel Z hZ)
  exact (iff_of_eq he).trans (hker U a)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.UniversalTarget.Construction
