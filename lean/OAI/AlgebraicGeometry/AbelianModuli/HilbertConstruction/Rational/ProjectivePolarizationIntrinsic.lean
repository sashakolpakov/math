import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.ProjectivePolarizationParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.InducingHom
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.CanonicalDualTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementBaseChange

/-! # Projective Polarization Intrinsic -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.ProjectivePolarizationIntrinsic.RationalProjectivePolarizationLocus

noncomputable section

/-! Intrinsic all-test classification of the rational projective
polarization locus. The enhancement may use any actual representing
dual. Its original geometric positivity supplies symmetry and forces
the division equation after canonical dual transport. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsNoetherianRing R] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of R))) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (L : Line.Bundles.LineBundle A.scheme.left) (qS : Spec (.of R) ⟶ Spec (.of ℚ)) (hL : L.IsAmple)
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i)

/-- Existence of an original graph-power polarization enhancement is
exactly the condition represented by the constructed monomorphism. -/
theorem parameter_hasPoint_iff_graphPowerEnhancement {N : ℕ}
    (level : A.FullLevel N) (T : Over (Spec (.of R))) :
    Nonempty (T ⟶ ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter A P L qS hL d hd δ hδ) ↔
      Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
        ((⟨A, level⟩ : Level.Data.AbelianSchemeWithFullLevel g N (Spec (.of R))).pullback T.hom)
        ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom T.hom)) d) := by
  let D := ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.dualData A P L qS hL
  let m := ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.inducingIsogeny A P L qS hL
  let DT := D.pullback T.hom
  let M := (A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom T.hom)
  let mb : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) DT.abelian := m.pullback T.hom
  constructor
  · intro h
    obtain ⟨p, hp, ht, hG⟩ := (ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter_hasPoint_iff A P L qS hL d hd δ hδ T).mp h
    let pol : PolarizationData.Polarization DT δ :=
      PolarizationData.Polarization.ofBaseChangedAmpleTranslationDivisor D T.hom p δ ht qS d hd
        m.hom L hL (ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.inducingPoincareRecovery A P L qS hL) hp hG.some
    exact ⟨{ dual := DT, polarization := pol, powerIso := hG }⟩
  · rintro ⟨H⟩
    obtain ⟨p, hG⟩ := GraphPower.CanonicalDualTransport.graphPowerEnhancement_on_chosenDual A P T DT mb
      (level.pullback T.hom) hδ M d H
    let em : (((DT.poincareAt mb.hom).tensor
        (M.pullback (fst (A.pullback T.hom).scheme (A.pullback T.hom).scheme).left)).tensor
        (M.pullback (snd (A.pullback T.hom).scheme (A.pullback T.hom).scheme).left)).sheaf ≅
          (M.pullback μ[(A.pullback T.hom).scheme].left).sheaf :=
      DivisorPolarization.inducingFormulaBaseChangeIso D m.hom (A.zeroNormalizedBundle L)
        (TranslationDivisorPolarization.translationDifferenceNormalizedInducingFormula D m.hom L
          (ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.inducingPoincareRecovery A P L qS hL)) T.hom
    have hp : (A.pullback T.hom).multiplication (2 * d) ≫ p.isogeny.hom = mb.hom :=
      GraphPower.InducingHom.polarization_inducingHom_eq_multiple_of_graphPower A P T DT p (level.pullback T.hom)
        hδ mb.hom (IsMonHom.one_hom mb.hom) M d em hG.some
    apply (ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter_hasPoint_iff A P L qS hL d hd δ hδ T).mpr
    exact ⟨p.isogeny, hp, p.kernelType, hG⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.ProjectivePolarizationIntrinsic.RationalProjectivePolarizationLocus
