import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Polarized
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.DualPoincare
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Rosati
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PELExistence

/-! # PEL -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PEL.Construction

noncomputable section

/-! The actual isotropic quotient with universal global functions is a full PEL object,
with the supplied descended action and ordered marking retained literally. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
  {d N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T)
  (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A.polarized.abelian.scheme)
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

include hA hσ hker hlag hc in
set_option backward.isDefEq.respectTransparency false in
theorem universalFunctionQuotient_full_pel_exists :
    ∃ (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) (p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB P.polarizationType),
      AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (Canonical.PELExistence.Construction.polarizedQuotientData B DB p level) σ ∧
      AbelianModuli.ReferenceFamily.PEL.Objects.HasPrescribedLieRanks P iota T B σ ∧
      f.hom ≫ p.isogeny.hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom A.polarized.dual DB =
        A.polarized.polarization.isogeny.hom ^ n := by
  obtain ⟨DB, hDB, p, hp⟩ := Polarized.Construction.universalFunction_isotropic_quotient_polarization_exists
    A.polarized.dual hA A.polarized.polarization f n hn hker hlag hc T.hom
  have hB := GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source f.hom hA
  refine ⟨DB, p, ?_, ?_, hp⟩
  · intro a
    refine ⟨FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (σ.map a) DB DB,
      DualMaps.Construction.universalFunction_nativeDualMap_isMonHom (σ.map a) DB DB hDB,
      DualPoincare.Construction.universalFunction_nativeDualMap_poincare DB DB hB (σ.map a), ?_⟩
    exact Rosati.Construction.universalFunction_picardQuotient_rosati_equation A.polarized.dual DB hB hDB f
      A.polarized.polarization.isogeny.hom p.isogeny.hom A.action σ hσ n hp a
      (NumberField.IsCMField.ringOfIntegersComplexConj E a)
      (FrobeniusKernel.PicardAdjoints.Construction.rosati_canonicalDual A.polarized A.action A.rosati a)
  · exact Intrinsic.Action.Construction.prescribed_lie_ranks_after_quotient P iota T A.polarized.abelian B A.action σ f
      (fun a => (hσ a).symm) A.lieRanks

def universalFunctionQuotientPEL : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T := by
  let H := universalFunctionQuotient_full_pel_exists A hA n hn f σ level hσ hker hlag hc
  exact {
    polarized := Canonical.PELExistence.Construction.polarizedQuotientData B H.choose H.choose_spec.choose level
    action := σ
    rosati := H.choose_spec.choose_spec.1
    lieRanks := H.choose_spec.choose_spec.2.1 }

theorem universalFunctionQuotientPEL_abelian :
    (universalFunctionQuotientPEL A hA n hn f σ level hσ hker hlag hc).polarized.abelian = B := rfl

theorem universalFunctionQuotientPEL_action :
    (universalFunctionQuotientPEL A hA n hn f σ level hσ hker hlag hc).action = σ := rfl

theorem universalFunctionQuotientPEL_level :
    (universalFunctionQuotientPEL A hA n hn f σ level hσ hker hlag hc).polarized.level = level := rfl

theorem universalFunctionQuotientPEL_polarization :
    let Q := universalFunctionQuotientPEL A hA n hn f σ level hσ hker hlag hc
    f.hom ≫ Q.polarized.polarization.isogeny.hom ≫
      FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom A.polarized.dual Q.polarized.dual =
        A.polarized.polarization.isogeny.hom ^ n :=
  (universalFunctionQuotient_full_pel_exists A hA n hn f σ level hσ hker hlag hc).choose_spec.choose_spec.2.2

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PEL.Construction
