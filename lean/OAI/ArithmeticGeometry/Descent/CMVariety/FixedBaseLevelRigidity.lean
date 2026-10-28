import OAI.ArithmeticGeometry.Descent.CMVariety.FixedSchemeLevelRigidity
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicBaseLevelRigidity

/-! # Fixed Base Level Rigidity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-! Native-base rigidity for every explicit CM enhancement, including full level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical ContDiff _root_.Manifold _root_.CategoryTheory.MonObj _root_.Topology

namespace FixedBaseLevelRigidity.Abelian.FamilyPoints

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ}

def FamilyRigidForCMEnhancementsWithLevelAlong {B : Type} [TopologicalSpace B]
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (present : ∀ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s.left))
    {levelOrder : ℕ} (level : G.FullLevel levelOrder)
    (parameter : B → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (q₀ : B) (s₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) : Prop :=
  ∀ enhancement : AlgebraicEnhancement.Abelian.CMEnhancement (present s₀).variety,
    ∀ k : Fin enhancement.size → (G.scheme ⟶ G.scheme),
      (∀ j, IsMonHom (k j)) →
      (∀ j, (present s₀).comparison.inv ≫ FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (k j) s₀ ≫
        (present s₀).comparison.hom = enhancement.map j) →
      ∀ᶠ q in 𝓝 q₀,
        IntrinsicBaseLevelRigidity.Abelian.FamilyPoints.PresentedEquivariantLevelFiberIso G present level s₀ enhancement.map k (parameter q)

def FamilyRigidForCMEnhancementsWithLevel (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (present : ∀ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s.left))
    {levelOrder : ℕ} (level : G.FullLevel levelOrder) (s₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) : Prop :=
  FamilyRigidForCMEnhancementsWithLevelAlong G present level id s₀ s₀

variable {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F]

theorem native_scheme_fixed_enhancement_level_rigidity_on_base
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (present : ∀ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s.left))
    (V : (AbelianFamilyPoints.FamilyPoints.total S G).left.Opens) (hV : IsAffineOpen V)
    {R : Type} [CommRing R] [Algebra ℂ R]
    [Algebra R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)]
    [IsScalarTower ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)]
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (hi : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) V hV ≫ AbelianFamilyPoints.FamilyPoints.projection S G =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)
        (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)) ≫ b)
    (σ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V →ₐ[ℂ] R)
    (hσ : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V) R σ ≫
          AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) V hV = b ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G)
    {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)}
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x σ)
    (levelOrder : ℕ) (hlevelOrder : 0 < levelOrder) (level : G.FullLevel levelOrder) :
    let s₀ := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b
      (x.comp (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)))
    FamilyRigidForCMEnhancementsWithLevel G present level s₀ := by
  dsimp only
  let y := x.comp (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V))
  let s₀ := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b y
  let a := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ R) b N.charts.base
  have hs₀ : s₀ ∈ a.source := ⟨y, N.charts.basePoint, rfl⟩
  have hac : a s₀ = N.charts.base y := OpenPartialHomeomorph.lift_openEmbedding_apply _ _
  have H := FixedSchemeLevelRigidity.Abelian.FamilyPoints.native_scheme_family_rigid_with_fixed_enhancement_and_level G present V hV b hi σ hσ N
    levelOrder hlevelOrder level
  dsimp only at H
  let parameter := fun q : F => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
  have H' : FamilyRigidForCMEnhancementsWithLevelAlong G present level parameter (N.charts.base y)
      (parameter (N.charts.base y)) := H
  have hcenter : parameter (N.charts.base y) = s₀ :=
    congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b)
      (N.charts.base.left_inv N.charts.basePoint)
  rw [hcenter] at H'
  intro enhancement k hk hk₀
  have h := H' enhancement k hk hk₀
  have h' : ∀ᶠ q : F in 𝓝 (a s₀),
      IntrinsicBaseLevelRigidity.Abelian.FamilyPoints.PresentedEquivariantLevelFiberIso G present level s₀ enhancement.map k (a.symm q) := by
    rw [hac]
    exact h
  have hev := (a.continuousAt hs₀).eventually h'
  filter_upwards [hev, a.open_source.mem_nhds hs₀] with s hs hsrc
  exact (congrArg (IntrinsicBaseLevelRigidity.Abelian.FamilyPoints.PresentedEquivariantLevelFiberIso G present level s₀ enhancement.map k)
    (a.left_inv hsrc)).mp hs

end FixedBaseLevelRigidity.Abelian.FamilyPoints

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R]
  {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left} {b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S} [IsOpenImmersion b.left]
  {Q : LocalizedSectionCharts.Abelian.RelativeCharts.ComplexPresentation R} {y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R}

theorem CanonicalIdentity.Abelian.RelativeCharts.CanonicalIdentityCharts.fixed_enhancement_level_rigidity (C : CanonicalIdentity.Abelian.RelativeCharts.CanonicalIdentityCharts G b Q y)
    (present : ∀ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s.left))
    (levelOrder : ℕ) (hlevelOrder : 0 < levelOrder) (level : G.FullLevel levelOrder) :
    let s₀ := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b y
    FixedBaseLevelRigidity.Abelian.FamilyPoints.FamilyRigidForCMEnhancementsWithLevel G present level s₀ := by
  have H := FixedBaseLevelRigidity.Abelian.FamilyPoints.native_scheme_fixed_enhancement_level_rigidity_on_base G present
    C.affineOpen C.isAffine b C.projection_eq C.sectionAlgebra C.section_eq C.charts
    levelOrder hlevelOrder level
  dsimp only at H
  have hbase : (y.comp C.sectionAlgebra).comp
      (IsScalarTower.toAlgHom ℂ R
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) C.affineOpen)) = y := by
    rw [AlgHom.comp_assoc, C.retraction, AlgHom.comp_id]
  rw [hbase] at H
  exact H

end

end OAI.ArithmeticGeometry.Descent.CMVariety
