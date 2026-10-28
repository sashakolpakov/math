import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.Polarized
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualPoincare
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.Rosati
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PELExistence

/-! # PEL -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PEL.Construction

noncomputable section

/-! The actual Noetherian isotropic quotient is a full PEL object,
with the supplied descended action and ordered marking retained literally. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
  {d N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))} [IsLocallyNoetherian T.left] (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T)
  (n : ℕ) (hn : 0 < n) {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * d) T.left}
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian B) [Etale f.hom.left]
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B) (level : B.FullLevel N)
  (hσ : ∀ a, A.action.map a ≫ f.hom = f.hom ≫ σ.map a)
  (hker : ∀ (U : Over T.left) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom), x ^ n = 1)
  (hlag : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ T.left),
    let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.polarized.abelian.pullback s).scheme n)
      (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (f.pullback s).hom)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.polarized.abelian.pullback s) (A.polarized.dual.pullback s)
      (A.polarized.polarization.pullback s) n hn).relativeAnnihilator H = H)
  (hc : Nat.Coprime n ((∏ j, P.polarizationType j) ^ 2))

include hσ hker hlag hc in
set_option backward.isDefEq.respectTransparency false in
theorem noetherianQuotient_full_pel_exists :
    ∃ (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) (p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB P.polarizationType),
      AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (Canonical.PELExistence.Construction.polarizedQuotientData B DB p level) σ ∧
      AbelianModuli.ReferenceFamily.PEL.Objects.HasPrescribedLieRanks P iota T B σ ∧
      f.hom ≫ p.isogeny.hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom A.polarized.dual DB =
        A.polarized.polarization.isogeny.hom ^ n := by
  obtain ⟨DB, p, hp⟩ := Polarized.Construction.noetherian_isotropic_quotient_polarization_exists
    A.polarized.dual A.polarized.polarization f n hn hker hlag hc T.hom
  refine ⟨DB, p, ?_, ?_, hp⟩
  · intro a
    refine ⟨FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (σ.map a) DB DB,
      DualMaps.Construction.noetherian_nativeDualMap_isMonHom (σ.map a) DB DB,
      DualPoincare.Construction.noetherian_nativeDualMap_poincare DB DB (σ.map a), ?_⟩
    exact Rosati.Construction.noetherian_picardQuotient_rosati_equation A.polarized.dual DB f
      A.polarized.polarization.isogeny.hom p.isogeny.hom A.action σ hσ n hp a
      (NumberField.IsCMField.ringOfIntegersComplexConj E a)
      (FrobeniusKernel.PicardAdjoints.Construction.rosati_canonicalDual A.polarized A.action A.rosati a)
  · exact Intrinsic.Action.Construction.prescribed_lie_ranks_after_quotient P iota T A.polarized.abelian B A.action σ f
      (fun a => (hσ a).symm) A.lieRanks

def noetherianQuotientPEL : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T := by
  let H := noetherianQuotient_full_pel_exists A n hn f σ level hσ hker hlag hc
  exact {
    polarized := Canonical.PELExistence.Construction.polarizedQuotientData B H.choose H.choose_spec.choose level
    action := σ
    rosati := H.choose_spec.choose_spec.1
    lieRanks := H.choose_spec.choose_spec.2.1 }

theorem noetherianQuotientPEL_abelian :
    (noetherianQuotientPEL A n hn f σ level hσ hker hlag hc).polarized.abelian = B := rfl

theorem noetherianQuotientPEL_action :
    (noetherianQuotientPEL A n hn f σ level hσ hker hlag hc).action = σ := rfl

theorem noetherianQuotientPEL_level :
    (noetherianQuotientPEL A n hn f σ level hσ hker hlag hc).polarized.level = level := rfl

theorem noetherianQuotientPEL_polarization :
    let Q := noetherianQuotientPEL A n hn f σ level hσ hker hlag hc
    f.hom ≫ Q.polarized.polarization.isogeny.hom ≫
      FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom A.polarized.dual Q.polarized.dual =
        A.polarized.polarization.isogeny.hom ^ n :=
  (noetherianQuotient_full_pel_exists A n hn f σ level hσ hker hlag hc).choose_spec.choose_spec.2.2

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PEL.Construction
