import OAI.ArithmeticGeometry.Descent.CMVariety.LocalizedCanonicalIdentityCharts
import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothBaseNeighborhood
import OAI.ArithmeticGeometry.Descent.CMVariety.AffineFamilyNeighborhood
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexPresentationDimension

/-! # Intrinsic Family Charts -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts

noncomputable section

/-! A smooth integral base and its actual abelian family construct
the canonical normalized charts, retaining the original center, affine
open immersion, integral coordinate algebra, and intrinsic dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

theorem affineOpenAlgebra_domain_of_point
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left]
    (R : CommAlgCat ℂ) (b : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) : IsDomain R := by
  let : Nonempty (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).left :=
    ⟨(Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv R y).left (Classical.arbitrary Foundations.Scheme.ProjectiveSpace.complexBase)⟩
  have h := isIntegral_of_isOpenImmersion b.left
  change IsIntegral (Spec (CommRingCat.of R)) at h
  exact (affine_isIntegral_iff (CommRingCat.of R)).mp h

structure NativeFamilyCharts {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ}
    (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (s₀ : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) where
  algebra : CommAlgCat ℂ
  [domain : IsDomain algebra]
  [smooth : Algebra.Smooth ℂ algebra]
  openMap : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ algebra ⟶ S
  [openImmersion : IsOpenImmersion openMap.left]
  point : Foundations.Scheme.AffineComplexPoints.affineComplexPoints algebra
  presentation : ArithmeticGeometry.Descent.CMVariety.LocalizedSectionCharts.Abelian.RelativeCharts.ComplexPresentation algebra
  charts : ArithmeticGeometry.Descent.CMVariety.CanonicalIdentity.Abelian.RelativeCharts.CanonicalIdentityCharts G openMap presentation point
  center : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap algebra openMap point = s₀

attribute [instance] NativeFamilyCharts.domain NativeFamilyCharts.smooth NativeFamilyCharts.openImmersion

theorem exists_native_family_charts
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom] {g : ℕ}
    (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (s₀ : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    Nonempty (NativeFamilyCharts G s₀) := by
  obtain ⟨R, b, hb, y, P, hy⟩ := ArithmeticGeometry.Descent.CMVariety.SmoothBaseNeighborhood.Abelian.RelativeCharts.exists_smooth_affine_base_neighborhood S s₀
  let : IsOpenImmersion b.left := hb
  let t : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) := s₀ ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.identitySection S G
  have hp : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) t = s₀ := by
    change (s₀ ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.identitySection S G) ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G = s₀
    rw [Category.assoc, ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.identitySection_projection, Category.comp_id]
  have ht : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) t ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map b) :=
    ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv R y, hy.trans hp.symm⟩
  obtain ⟨A, a, tower, i, hI, hi, hunit⟩ := ArithmeticGeometry.Descent.CMVariety.AffineFamilyNeighborhood.Abelian.RelativeCharts.exists_affine_diagram_over_open (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) b t ht
  let : Algebra R A := a
  let : IsScalarTower ℂ R A := tower
  let : IsOpenImmersion i.left := hI
  have hunit' : (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap R b y ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.identitySection S G) ∈
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) := by
    rw [hy]
    exact hunit
  obtain ⟨c, hc, Q, ⟨C⟩⟩ := ArithmeticGeometry.Descent.CMVariety.LocalizedCanonicalIdentityCharts.Abelian.RelativeCharts.exists_localized_canonical_identity_charts G b i hi P y hunit'
  let R' := CommAlgCat.of ℂ (Localization.Away c)
  let b' := ArithmeticGeometry.Descent.CMVariety.LocalizedFamily.Abelian.RelativeCharts.affineAwayMap c ≫ b
  let : IsOpenImmersion b'.left := by
    change IsOpenImmersion ((ArithmeticGeometry.Descent.CMVariety.LocalizedFamily.Abelian.RelativeCharts.affineAwayMap c).left ≫ b.left)
    infer_instance
  let y' := Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint y c hc
  let : IsDomain R' := affineOpenAlgebra_domain_of_point R' b' y'
  let : Algebra.IsStandardSmooth ℂ R' := Q.presentation.isStandardSmooth
  exact ⟨{
    algebra := R'
    domain := inferInstance
    smooth := inferInstance
    openMap := b'
    openImmersion := inferInstance
    point := y'
    presentation := Q
    charts := C
    center := (ArithmeticGeometry.Descent.CMVariety.LocalizedFamily.Abelian.RelativeCharts.affineAwayMap_point b y c hc).trans hy }⟩

theorem NativeFamilyCharts.dimension
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom] {g : ℕ}
    {G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left} {s₀ : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    (C : NativeFamilyCharts G s₀) :
    Module.finrank ℂ (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates C.presentation.presentation.map → ℂ) =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom :=
  ComplexPresentationDimension.complexPresentation_dimension C.algebra C.openMap C.presentation C.point

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts
