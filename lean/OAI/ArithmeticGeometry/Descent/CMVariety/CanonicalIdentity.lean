import OAI.ArithmeticGeometry.Descent.CMVariety.CanonicalAffineSection
import OAI.ArithmeticGeometry.Descent.CMVariety.LocalizedSectionCharts
import OAI.ArithmeticGeometry.Descent.CMVariety.FiberChartProjection

/-! # Canonical Identity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.CanonicalIdentity.Abelian.RelativeCharts

noncomputable section

/-!
Construct the canonical affine-open identity charts required by the native
abelian-family rigidity theorem, from an actual affine section diagram.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ}
  {R A : Type} [CommRing R] [Algebra ℂ R] [CommRing A] [Algebra ℂ A]

structure CanonicalIdentityCharts
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S)
    (Q : LocalizedSectionCharts.Abelian.RelativeCharts.ComplexPresentation R) (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) where
  affineOpen : (AbelianFamilyPoints.FamilyPoints.total S G).left.Opens
  isAffine : IsAffineOpen affineOpen
  [baseAlgebra : Algebra R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) affineOpen)]
  [baseScalarTower : IsScalarTower ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) affineOpen)]
  sectionAlgebra : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) affineOpen →ₐ[ℂ] R
  projection_eq : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) affineOpen isAffine ≫
      AbelianFamilyPoints.FamilyPoints.projection S G =
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) affineOpen)
      (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) affineOpen)) ≫ b
  section_eq : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) affineOpen) R sectionAlgebra ≫
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) affineOpen isAffine =
      b ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G
  retraction : sectionAlgebra.comp
      (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) affineOpen)) =
        AlgHom.id ℂ R
  relativePresentation : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.RelativePresentationAt (R := R) (y.comp sectionAlgebra)
  charts : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts
    (E := AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates relativePresentation.presentation.map → ℂ)
    (F := AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates Q.presentation.map → ℂ) (y.comp sectionAlgebra) sectionAlgebra

attribute [instance] CanonicalIdentityCharts.baseAlgebra CanonicalIdentityCharts.baseScalarTower

/-- The smooth abelian scheme and actual algebraic section construct
all the canonical affine-open data and the normalized analytic charts. -/
theorem exists_canonical_identity_charts
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ AbelianFamilyPoints.FamilyPoints.total S G) [IsOpenImmersion i.left]
    (f : R →ₐ[ℂ] A) (σ : A →ₐ[ℂ] R)
    (hi : i ≫ AbelianFamilyPoints.FamilyPoints.projection S G = AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A f ≫ b)
    (hσ : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A R σ ≫ i = b ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G)
    (Q : LocalizedSectionCharts.Abelian.RelativeCharts.ComplexPresentation R) (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) :
    Nonempty (CanonicalIdentityCharts G b Q y) := by
  obtain ⟨V, hV, a, ht, σ', hp, hs, hret⟩ := CanonicalAffineSection.Abelian.RelativeCharts.exists_canonical_affine_section_diagram
    (AbelianFamilyPoints.FamilyPoints.projection S G) (AbelianFamilyPoints.FamilyPoints.identitySection S G)
    (AbelianFamilyPoints.FamilyPoints.identitySection_projection S G) b i f σ hi hσ
  let : Algebra R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V) := a
  let : IsScalarTower ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V) := ht
  let : Smooth (AbelianFamilyPoints.FamilyPoints.projection S G).left := inferInstanceAs (Smooth G.scheme.hom)
  let : Algebra.Smooth R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V) :=
    FiberChartProjection.Abelian.RelativeCharts.algebraSmooth_of_nativeDiagram (AbelianFamilyPoints.FamilyPoints.projection S G) b
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) V hV) hp
  have hx : ((y.comp σ').comp
      (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V))).comp σ' =
        y.comp σ' := by
    rw [AlgHom.comp_assoc y, hret, AlgHom.comp_id]
  obtain ⟨D, ⟨N⟩⟩ := RegularSectionCharts.Abelian.RelativeCharts.exists_smooth_relative_section_charts Q.presentation (y.comp σ') σ' hret hx
  exact ⟨{
    affineOpen := V
    isAffine := hV
    baseAlgebra := a
    baseScalarTower := ht
    sectionAlgebra := σ'
    projection_eq := hp
    section_eq := hs
    retraction := hret
    relativePresentation := D
    charts := N }⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.CanonicalIdentity.Abelian.RelativeCharts
