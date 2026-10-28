import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.PolarizationParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.InducingHom
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.CanonicalDualTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementParameterPullback

/-! # Polarization Intrinsic -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.PolarizationIntrinsic.UnitPolarizationLocus

noncomputable section

/-! The unit-based polarization locus represents the original graph-power
enhancement, allowing the enhancement to use any actual representing dual. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S] {g : ℕ}
    {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A)
    (m : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) [Etale m.hom.left]
    (d : ℕ) (hunit : IsUnit ((2 * d : ℕ) : Γ(S, ⊤)))
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i) (hd : 0 < d) (hL : L.IsAmple)
    (recover : (D.poincare.pullback (m.hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf)

def universalEnhancement {N : ℕ} (level : A.FullLevel N) :
    GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
      ((⟨A, level⟩ : Level.Data.AbelianSchemeWithFullLevel g N S).pullback
        (PolarizationParameter.UnitPolarizationLocus.parameter D m d hunit P L δ hδ).hom)
      ((A.zeroNormalizedBundle L).pullback
        (pullback.fst A.scheme.hom (PolarizationParameter.UnitPolarizationLocus.parameter D m d hunit P L δ hδ).hom)) d where
  dual := D.pullback (PolarizationParameter.UnitPolarizationLocus.parameter D m d hunit P L δ hδ).hom
  polarization := PolarizationParameter.UnitPolarizationLocus.polarization D m d hunit P L δ hδ hd hL recover
  powerIso := ⟨PolarizationParameter.UnitPolarizationLocus.universalIso D m d hunit P L δ hδ⟩

include hd hL recover in
theorem parameter_hasPoint_iff_graphPowerEnhancement {N : ℕ}
    (level : A.FullLevel N) (T : Over S) :
    Nonempty (T ⟶ PolarizationParameter.UnitPolarizationLocus.parameter D m d hunit P L δ hδ) ↔
      Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
        ((⟨A, level⟩ : Level.Data.AbelianSchemeWithFullLevel g N S).pullback T.hom)
        ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom T.hom)) d) := by
  let : IsNoetherian S := ⟨⟩
  let DT := D.pullback T.hom
  let M := (A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom T.hom)
  let mb : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) DT.abelian := m.pullback T.hom
  constructor
  · rintro ⟨a⟩
    exact ⟨GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.parameterPullback
      (F := (⟨A, level⟩ : Level.Data.AbelianSchemeWithFullLevel g N S))
      (L := A.zeroNormalizedBundle L) (d := d)
      (T := PolarizationParameter.UnitPolarizationLocus.parameter D m d hunit P L δ hδ) (U := T)
      (universalEnhancement (S := S) (g := g) (A := A) (D := D) (m := m)
        (d := d) (hunit := hunit) (P := P) (L := L) (δ := δ) (hδ := hδ)
        (hd := hd) (hL := hL) (recover := recover) (N := N) (level := level)) a⟩
  · rintro ⟨H⟩
    obtain ⟨p, hG⟩ := GraphPower.CanonicalDualTransport.graphPowerEnhancement_on_chosenDual A P T DT mb
      (level.pullback T.hom) hδ M d H
    let em : (((DT.poincareAt mb.hom).tensor
        (M.pullback (fst (A.pullback T.hom).scheme (A.pullback T.hom).scheme).left)).tensor
        (M.pullback (snd (A.pullback T.hom).scheme (A.pullback T.hom).scheme).left)).sheaf ≅
          (M.pullback μ[(A.pullback T.hom).scheme].left).sheaf :=
      Rational.DivisorPolarization.inducingFormulaBaseChangeIso D m.hom (A.zeroNormalizedBundle L)
        (Rational.TranslationDivisorPolarization.translationDifferenceNormalizedInducingFormula D m.hom L recover) T.hom
    have hp : (A.pullback T.hom).multiplication (2 * d) ≫ p.isogeny.hom = mb.hom :=
      GraphPower.InducingHom.polarization_inducingHom_eq_multiple_of_graphPower A P T DT p (level.pullback T.hom)
        hδ mb.hom (IsMonHom.one_hom mb.hom) M d em hG.some
    apply (PolarizationParameter.UnitPolarizationLocus.parameter_hasPoint_iff D m d hunit P L δ hδ T).mpr
    exact ⟨p.isogeny, hp, p.kernelType, hG⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.PolarizationIntrinsic.UnitPolarizationLocus
