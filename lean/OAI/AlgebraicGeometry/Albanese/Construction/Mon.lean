import OAI.AlgebraicGeometry.Albanese.Construction.Smooth
import OAI.AlgebraicGeometry.Albanese.Construction.Rigidity
import OAI.AlgebraicGeometry.Albanese.Construction.GeneratedClosed
import OAI.AlgebraicGeometry.Albanese.Construction.RefinementBound
import OAI.AlgebraicGeometry.Albanese.Construction.EtaleMono
import OAI.AlgebraicGeometry.Albanese.Construction.Trivial
import OAI.AlgebraicGeometry.Albanese.Construction.MaximalRefinement
import OAI.AlgebraicGeometry.Albanese.Construction.SegreLocal
import OAI.AlgebraicGeometry.Albanese.Construction.Bounded
import OAI.AlgebraicGeometry.Albanese.Construction.DimensionBound

/-! # Mon -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.Mon

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

section

/-!
Construction: unconditional Albanese existence for the specified connected smooth
projective complex schemes. Point differences construct generated abelian
subvarieties. Segre projective products provide common generated targets.
Invariant holomorphic one-forms inject into the source's finite-dimensional
first de Rham cohomology, bounding every generated target's dimension.
Equal-dimensional refinements are finite étale, with fiber sizes bounded by
a fixed word fiber. Maximizing dimension and then the finite fiber size
produces the universal target; generation proves uniqueness.
The committed specification's identity-point numerals require the MonObj scope
opened above. No statement placeholder is imported here.
-/

/-- The canonical morphism from a complex variety to the complex base. -/
def toBase (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    X.toOver ⟶ Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) :=
  Over.homMk X.structureMap (by simp)

/-- A complex point is a section of the structure map. -/
@[simp]
theorem point_toBase (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) :
    x₀ ≫ toBase X = 𝟙 _ := by
  ext
  exact x₀.w

/-- Subtracting the value at the base point is an algebraic morphism. -/
def normalize (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver) :
    X.toOver ⟶ A.toOver :=
  f / (toBase X ≫ x₀ ≫ f)

/-- The normalized morphism sends the chosen point to the identity. -/
@[simp]
theorem normalize_point (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver) :
    x₀ ≫ normalize X x₀ A f = 1 := by
  simp [normalize, GrpObj.comp_div, ← Category.assoc]

/-- Normalizing an already pointed morphism leaves it unchanged. -/
theorem normalize_of_pointed (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver)
    (hf : x₀ ≫ f = 1) :
    normalize X x₀ A f = f := by
  simp [normalize, hf]

/-- Normalization is compatible with algebraic group homomorphisms. -/
theorem normalize_comp (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver)
    (g : A.toOver ⟶ B.toOver) [IsMonHom g] :
    normalize X x₀ A f ≫ g = normalize X x₀ B (f ≫ g) := by
  simp [normalize, GrpObj.div_comp, Category.assoc]

/-- Evaluation of a normalized map is the corresponding point difference. -/
theorem point_normalize (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x₀ x : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver) :
    x ≫ normalize X x₀ A f = (x ≫ f) / (x₀ ≫ f) := by
  simp [normalize, GrpObj.comp_div, ← Category.assoc]

/-- A pointed algebraic morphism between complex abelian varieties preserves
their group operations. The integrality condition needed by rigidity is proved. -/
theorem abelian_pointed_isMonHom (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : A.toOver ⟶ B.toOver)
    (hf : (1 : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.toOver) ≫ f = 1) :
    IsMonHom f := by
  have : IsProper A.toOver.hom := A.variety.presentation.projective.isProper
  have : IsProper B.toOver.hom := B.variety.presentation.projective.isProper
  have : IsIntegral (A.toOver ⊗ A.toOver).left := Smooth.abelian_tensor_integral A
  apply Rigidity.isMonHom_of_pointed_of_integral_product A.toOver B.toOver f
  simpa only [MonObj.one_eq_one] using hf

/-- Subtracting the value at the identity turns any algebraic morphism of
complex abelian varieties into an algebraic group homomorphism. -/
theorem abelian_normalize_isMonHom (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : A.toOver ⟶ B.toOver) :
    IsMonHom (normalize A.variety.presentation 1 B f) := by
  apply abelian_pointed_isMonHom A B
  exact normalize_point A.variety.presentation 1 B f

end

/-- Construction: Albanese existence and its pointed universal property. -/
theorem exists_albanese
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier]
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) :
    ∃ (Alb : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ Alb.toOver),
      x₀ ≫ a = 1 ∧
      ∀ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver),
        x₀ ≫ f = 1 →
        ∃! φ : Alb.toOver ⟶ A.toOver,
          IsMonHom φ ∧ a ≫ φ = f := by
  apply Bounded.exists_albanese_of_dimension_bound X x₀
    (Module.finrank ℂ ((GeneratingForms.connectedVariety X).deRhamCohomology 1))
  intro A a _ hgen
  exact DimensionBound.generated_target_dimension_le X A a x₀ hgen

end

end OAI.AlgebraicGeometry.Albanese.Construction.Mon
