import OAI.ArithmeticGeometry.Descent.CMVariety.CanonicalIdentity
import OAI.ArithmeticGeometry.Descent.CMVariety.LocalizedFamily

/-! # Localized Canonical Identity Charts -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.LocalizedCanonicalIdentityCharts.Abelian.RelativeCharts

noncomputable section

/-!
Starting only with an actual affine base/total diagram and the central
identity point, construct a principal base neighborhood, its actual
identity section, and canonical affine-open normalized product charts.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ}
  {R A : Type} [CommRing R] [Algebra ℂ R] [CommRing A] [Algebra ℂ A]
  [Algebra R A] [IsScalarTower ℂ R A]

/-- The actual unit map supplies the localized section automatically;
the output is the canonical affine-open chart data used by CM rigidity. -/
theorem exists_localized_canonical_identity_charts
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ AbelianFamilyPoints.FamilyPoints.total S G) [IsOpenImmersion i.left]
    (hi : i ≫ AbelianFamilyPoints.FamilyPoints.projection S G =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (P : LocalizedSectionCharts.Abelian.RelativeCharts.ComplexPresentation R) (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R)
    (hy : (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b y ≫
      AbelianFamilyPoints.FamilyPoints.identitySection S G) ∈
        Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i)) :
    ∃ (a : R) (ha : y a ≠ 0) (Q : LocalizedSectionCharts.Abelian.RelativeCharts.ComplexPresentation (Localization.Away a)),
      Nonempty (CanonicalIdentity.Abelian.RelativeCharts.CanonicalIdentityCharts G (LocalizedFamily.Abelian.RelativeCharts.affineAwayMap a ≫ b) Q (AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint y a ha)) := by
  obtain ⟨a, ha, σ, hfac, hret, _⟩ := LocalizedFamily.Abelian.RelativeCharts.exists_identitySection_localization G b i hi y hy
  obtain ⟨Q⟩ : Nonempty (LocalizedSectionCharts.Abelian.RelativeCharts.ComplexPresentation (Localization.Away a)) := ⟨{
    VariableIndex := Unit ⊕ P.VariableIndex
    RelationIndex := Unit ⊕ P.RelationIndex
    presentation := (Algebra.SubmersivePresentation.localizationAway (Localization.Away a) a).comp P.presentation }⟩
  refine ⟨a, ha, Q, ?_⟩
  let b' := LocalizedFamily.Abelian.RelativeCharts.affineAwayMap a ≫ b
  let i' := LocalizedFamily.Abelian.RelativeCharts.affineAwayMap (algebraMap R A a) ≫ i
  let : IsOpenImmersion b'.left := by
    change IsOpenImmersion ((LocalizedFamily.Abelian.RelativeCharts.affineAwayMap a).left ≫ b.left)
    infer_instance
  let : IsOpenImmersion i'.left := by
    change IsOpenImmersion ((LocalizedFamily.Abelian.RelativeCharts.affineAwayMap (algebraMap R A a)).left ≫ i.left)
    infer_instance
  exact CanonicalIdentity.Abelian.RelativeCharts.exists_canonical_identity_charts G b' i' (LocalizedFamily.Abelian.RelativeCharts.localizedBaseMap (A := A) a)
    (LocalizedFamily.Abelian.RelativeCharts.localizedSection a σ hret)
    (LocalizedFamily.Abelian.RelativeCharts.localized_affine_projection (AbelianFamilyPoints.FamilyPoints.projection S G) b i hi a)
    (LocalizedFamily.Abelian.RelativeCharts.localized_affine_section (AbelianFamilyPoints.FamilyPoints.identitySection S G) b i a σ hret hfac)
    Q (AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint y a ha)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.LocalizedCanonicalIdentityCharts.Abelian.RelativeCharts
