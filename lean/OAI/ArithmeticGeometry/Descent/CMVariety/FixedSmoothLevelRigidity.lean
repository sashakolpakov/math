import OAI.ArithmeticGeometry.Descent.CMVariety.FixedBaseLevelRigidity
import OAI.ArithmeticGeometry.Descent.CMVariety.LocalizedCanonicalIdentityCharts
import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothBaseNeighborhood
import OAI.ArithmeticGeometry.Descent.CMVariety.AffineFamilyNeighborhood

/-! # Fixed Smooth Level Rigidity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FixedSmoothLevelRigidity

noncomputable section

/-!
Every explicit CM enhancement is locally rigid with full level in an
actual smooth-base abelian family. The enhancement can be chosen and
spread before constructing any local charts.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Abelian.RelativeCharts

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ}
  {R A : Type} [CommRing R] [Algebra ℂ R] [CommRing A] [Algebra ℂ A]
  [Algebra R A] [IsScalarTower ℂ R A]

theorem fixed_enhancement_level_rigidity_of_smooth_affine_diagram
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (present : ∀ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s.left))
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ AbelianFamilyPoints.FamilyPoints.total S G) [IsOpenImmersion i.left]
    (hi : i ≫ AbelianFamilyPoints.FamilyPoints.projection S G =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (P : LocalizedSectionCharts.Abelian.RelativeCharts.ComplexPresentation R) (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R)
    (hy : (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b y ≫
      AbelianFamilyPoints.FamilyPoints.identitySection S G) ∈
        Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i))
    (levelOrder : ℕ) (hlevelOrder : 0 < levelOrder) (level : G.FullLevel levelOrder) :
    let s₀ := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b y
    FixedBaseLevelRigidity.Abelian.FamilyPoints.FamilyRigidForCMEnhancementsWithLevel G present level s₀ := by
  obtain ⟨a, ha, Q, ⟨C⟩⟩ := LocalizedCanonicalIdentityCharts.Abelian.RelativeCharts.exists_localized_canonical_identity_charts G b i hi P y hy
  let b' := LocalizedFamily.Abelian.RelativeCharts.affineAwayMap a ≫ b
  let : IsOpenImmersion b'.left := by
    change IsOpenImmersion ((LocalizedFamily.Abelian.RelativeCharts.affineAwayMap a).left ≫ b.left)
    infer_instance
  have H := C.fixed_enhancement_level_rigidity present levelOrder hlevelOrder level
  dsimp only at H
  rw [LocalizedFamily.Abelian.RelativeCharts.affineAwayMap_point] at H
  exact H

end Abelian.RelativeCharts

namespace Abelian.FamilyPoints

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth S.hom] {g : ℕ}

theorem smooth_base_family_rigid_for_cm_enhancements_with_level
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (present : ∀ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s.left))
    (levelOrder : ℕ) (hlevelOrder : 0 < levelOrder) (level : G.FullLevel levelOrder)
    (s₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    FixedBaseLevelRigidity.Abelian.FamilyPoints.FamilyRigidForCMEnhancementsWithLevel G present level s₀ := by
  obtain ⟨R, b, hb, y, P, hy⟩ := SmoothBaseNeighborhood.Abelian.RelativeCharts.exists_smooth_affine_base_neighborhood S s₀
  let : IsOpenImmersion b.left := hb
  let t : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AbelianFamilyPoints.FamilyPoints.total S G) := s₀ ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G
  have hp : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.projection S G) t = s₀ := by
    change (s₀ ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G) ≫ AbelianFamilyPoints.FamilyPoints.projection S G = s₀
    rw [Category.assoc, AbelianFamilyPoints.FamilyPoints.identitySection_projection, Category.comp_id]
  have ht : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.projection S G) t ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map b) :=
    ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv R y, hy.trans hp.symm⟩
  obtain ⟨A, a, tower, i, hI, hi, hunit⟩ :=
    AffineFamilyNeighborhood.Abelian.RelativeCharts.exists_affine_diagram_over_open (AbelianFamilyPoints.FamilyPoints.projection S G) b t ht
  let : Algebra R A := a
  let : IsScalarTower ℂ R A := tower
  let : IsOpenImmersion i.left := hI
  have hunit' : (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap R b y ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G) ∈
      Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) := by
    rw [hy]
    exact hunit
  have H := RelativeCharts.fixed_enhancement_level_rigidity_of_smooth_affine_diagram
    G present b i hi P y hunit' levelOrder hlevelOrder level
  dsimp only at H
  change FixedBaseLevelRigidity.Abelian.FamilyPoints.FamilyRigidForCMEnhancementsWithLevel G present level
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap R b y) at H
  rw [hy] at H
  exact H

end Abelian.FamilyPoints

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FixedSmoothLevelRigidity
