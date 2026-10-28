import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffinePointMaps
import Mathlib.Topology.Order

/-! # Scheme Point Homeomorphs -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-!
# Complex points of schemes and their affine-test topology

The carrier is the actual type of morphisms over `Spec ℂ` from the complex
point. Its topology is final with respect to all maps from ordinary affine
complex point spaces induced by actual morphisms of schemes over `Spec ℂ`.
This definition uses no chosen atlas or additional geometric data.

This file proves the universal continuity criterion, functoriality, and exact
recovery of the ordinary evaluation topology for affine schemes. Recovery
along arbitrary open immersions is a separate gluing theorem.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Genuine complex-valued points of a scheme over the complex base. -/
abbrev schemeComplexPoints (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) := (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X)

/-- The standard affine-character correspondence with the native scheme-point carrier. -/
abbrev affineSchemePointEquiv (A : Type) [CommRing A] [Algebra ℂ A] :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints A ≃ schemeComplexPoints (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A) :=
  Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A

/-- The native affine-point correspondence commutes with the genuine scheme maps. -/
@[simp]
theorem affineSchemePointEquiv_comap {A B : Type}
    [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    affineSchemePointEquiv A (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x) =
      affineSchemePointEquiv B x ≫ Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B f := by
  change Foundations.Scheme.AffineComplexPoints.affineComplexBaseIso.inv ≫
      Foundations.Scheme.AffineComplexPoints.affineComplexPointsEquiv A (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x) =
    (Foundations.Scheme.AffineComplexPoints.affineComplexBaseIso.inv ≫ Foundations.Scheme.AffineComplexPoints.affineComplexPointsEquiv B x) ≫ _
  rw [AffinePointMaps.affineComplexPointsEquiv_comap, Category.assoc]

namespace schemeComplexPoints

variable {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- Postcomposition is the actual covariant map on complex-valued points. -/
def map (f : X ⟶ Y) (x : schemeComplexPoints X) : schemeComplexPoints Y := x ≫ f

@[simp]
theorem map_id (x : schemeComplexPoints X) : schemeComplexPoints.map (𝟙 X) x = x := Category.comp_id x

@[simp]
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : schemeComplexPoints X) :
    schemeComplexPoints.map (f ≫ g) x = schemeComplexPoints.map g (schemeComplexPoints.map f x) := (Category.assoc x f g).symm

/-- A genuine affine scheme map induces this map from ordinary affine complex points. -/
def affinePointMap (A : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) : schemeComplexPoints X :=
  affineSchemePointEquiv A x ≫ f

@[simp]
theorem affinePointMap_comp (A : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (g : X ⟶ Y) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    affinePointMap A (f ≫ g) x = schemeComplexPoints.map g (affinePointMap A f x) :=
  (Category.assoc _ _ _).symm

/-- Algebra-map precomposition agrees with composition of the corresponding affine tests. -/
theorem affinePointMap_comap (A B : CommAlgCat ℂ) (f : A →ₐ[ℂ] B)
    (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    affinePointMap B (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B f ≫ g) x =
      affinePointMap A g (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x) := by
  change affineSchemePointEquiv B x ≫ (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B f ≫ g) =
    affineSchemePointEquiv A (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x) ≫ g
  rw [affineSchemePointEquiv_comap, Category.assoc]

/-- The topology final with respect to all actual affine complex-point test maps. -/
@[instance_reducible]
def analyticTopology (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : TopologicalSpace (schemeComplexPoints X) :=
  ⨆ (A : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X),
    TopologicalSpace.coinduced (affinePointMap A f) inferInstance

instance instTopologicalSpace (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    TopologicalSpace (schemeComplexPoints X) := analyticTopology X

/-- Each affine test map is continuous by construction of the final topology. -/
theorem continuous_affinePointMap (A : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) :
    Continuous (affinePointMap A f) := by
  apply continuous_iff_coinduced_le.mpr
  exact le_iSup_of_le A (le_iSup_of_le f le_rfl)

/-- A map from scheme points is continuous exactly when every affine test is continuous. -/
theorem continuous_iff_affineTests {T : Type*} [TopologicalSpace T]
    (F : schemeComplexPoints X → T) :
    Continuous F ↔ ∀ (A : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X),
      Continuous (fun x => F (affinePointMap A f x)) := by
  change @Continuous _ _ (analyticTopology X) _ F ↔ _
  simp only [continuous_iSup_dom, continuous_coinduced_dom,
    Function.comp_def]

/-- Openness in the final topology can be tested on every actual affine scheme map. -/
theorem isOpen_iff_affineTests (S : Set (schemeComplexPoints X)) :
    IsOpen S ↔ ∀ (A : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X),
      IsOpen (affinePointMap A f ⁻¹' S) := by
  change @IsOpen _ (analyticTopology X) S ↔ _
  simp only [isOpen_iSup_iff, isOpen_coinduced]

/-- Every morphism of complex schemes gives a continuous map on these complex points. -/
theorem continuous_map (f : X ⟶ Y) : Continuous (schemeComplexPoints.map f) := by
  apply (continuous_iff_affineTests _).mpr
  intro A g
  change Continuous (fun x => (affineSchemePointEquiv A x ≫ g) ≫ f)
  have h : Continuous (fun x => affineSchemePointEquiv A x ≫ (g ≫ f)) :=
    continuous_affinePointMap A (g ≫ f)
  simpa only [Category.assoc] using h

/-- The bundled continuous map on complex points induced by a scheme morphism. -/
def mapContinuous (f : X ⟶ Y) : C(schemeComplexPoints X, schemeComplexPoints Y) :=
  ⟨schemeComplexPoints.map f, continuous_map f⟩

end schemeComplexPoints

/-- On an actual affine scheme, the final topology is exactly the ordinary
evaluation topology on complex algebra characters. -/
def affineSchemePointHomeomorph (A : Type) [CommRing A] [Algebra ℂ A] :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints A ≃ₜ schemeComplexPoints (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A) where
  toEquiv := affineSchemePointEquiv A
  continuous_toFun := by
    have h : Continuous (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A =>
        affineSchemePointEquiv A x ≫ 𝟙 (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A)) :=
      schemeComplexPoints.continuous_affinePointMap (CommAlgCat.of ℂ A)
        (𝟙 (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A))
    exact h.congr fun x => Category.comp_id _
  continuous_invFun := by
    apply (schemeComplexPoints.continuous_iff_affineTests _).mpr
    intro B f
    obtain ⟨g, rfl⟩ := (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B).surjective f
    change Continuous (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B => (affineSchemePointEquiv A).symm
      (affineSchemePointEquiv B x ≫ Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B g))
    simp only [← affineSchemePointEquiv_comap, Equiv.symm_apply_apply]
    exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap g).continuous

/-- Complex points with the affine-test topology form a covariant topological functor. -/
def schemeComplexPointsFunctor : Over Foundations.Scheme.ProjectiveSpace.complexBase ⥤ TopCat where
  obj X := TopCat.of (schemeComplexPoints X)
  map f := TopCat.ofHom (schemeComplexPoints.mapContinuous f)
  map_id X := by
    apply TopCat.ext
    intro x
    exact schemeComplexPoints.map_id x
  map_comp f g := by
    apply TopCat.ext
    intro x
    exact schemeComplexPoints.map_comp f g x

end AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

namespace AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints

/-!
# Homeomorphisms of genuine complex scheme points

An isomorphism of schemes over the complex base induces a homeomorphism of
their actual complex-valued point spaces with the affine-test topology.
-/

open _root_.CategoryTheory

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- An actual scheme isomorphism gives a homeomorphism of complex-point spaces. -/
def isoHomeomorph (e : X ≅ Y) : schemeComplexPoints X ≃ₜ schemeComplexPoints Y where
  toFun := schemeComplexPoints.map e.hom
  invFun := schemeComplexPoints.map e.inv
  left_inv x := by
    change (x ≫ e.hom) ≫ e.inv = x
    simp only [Category.assoc, e.hom_inv_id, Category.comp_id]
  right_inv y := by
    change (y ≫ e.inv) ≫ e.hom = y
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  continuous_toFun := continuous_map e.hom
  continuous_invFun := continuous_map e.inv

@[simp]
theorem isoHomeomorph_apply (e : X ≅ Y) (x : schemeComplexPoints X) :
    isoHomeomorph e x = x ≫ e.hom := rfl

@[simp]
theorem isoHomeomorph_symm_apply (e : X ≅ Y) (y : schemeComplexPoints Y) :
    (isoHomeomorph e).symm y = y ≫ e.inv := rfl

end AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints

end

end OAI
